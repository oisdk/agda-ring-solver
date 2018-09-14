{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary
open import Relation.Nullary
open import Algebra.Solver.Ring.AlmostCommutativeRing as ACR

module Polynomials.Ring.Reflection
  {ℓ₁ ℓ₂}
  (ring : AlmostCommutativeRing ℓ₁ ℓ₂)
  (_≈?_ : Decidable (AlmostCommutativeRing._≈_ ring))
  where

open import Reflection
open AlmostCommutativeRing ring hiding (zero)
open import Data.Maybe
import Polynomials.Ring.Expr
module Expr′ = Polynomials.Ring.Expr rawRing (_≈ 0#) (λ x → x ≈? 0#) ring (ACR.-raw-almostCommutative⟶ ring) (λ x z → z)
open Expr′ using (Expr; _⊕_; ⊝_; _⊗_; Κ; Ι) public
open Expr′

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Fin as Fin
open import Data.List
open import Data.Unit

plus : Name
plus = quote _+_

mult : Name
mult = quote _*_

neg : Name
neg = quote -_

ringtype : Type
ringtype = def (quote Carrier) []

_>>=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

ringLiteral : ∀ {i} → Term → TC (Expr i)
ringLiteral x = do
  y ← checkType x ringtype
  z ← unquoteTC y
  returnTC (Κ z)

toExpr : ∀ {i} → Term → TC (Expr i)
toExpr {i} (var x args) with suc x ℕ.≤? i
toExpr {i} (var x args) | yes p = returnTC (Ι (Fin.fromℕ≤ p))
toExpr {i} (var x args) | no ¬p = typeError (strErr "unbound variable" ∷ [])
toExpr {i} (lam v t) = typeError (strErr "lambda" ∷ [])
toExpr {i} (pat-lam cs args) = typeError (strErr "lambda" ∷ [])
toExpr {i} (pi a b) = typeError (strErr "pi" ∷ [])
toExpr {i} (sort s) = typeError (strErr "sort" ∷ [])
toExpr {i} (meta x x₁) = typeError (strErr "meta" ∷ [])
toExpr {i} unknown = typeError (strErr "unknown" ∷ [])
toExpr {i} (con c args) = ringLiteral (con c args)
toExpr {i} (lit l) = ringLiteral (lit l)
toExpr {i} (def f args) with f ≟-Name neg | f ≟-Name plus | f ≟-Name mult
toExpr {i} (def f []) | yes p₁ | p | m = typeError (strErr "no args to neg" ∷ [])
toExpr {i} (def f (arg i₁ x ∷ args)) | yes p₁ | p | m = do
  x′ ← toExpr x
  returnTC (⊝ x′)
toExpr {i} (def f []) | no ¬p | yes p | m = typeError (strErr "not enough args to plus" ∷ [])
toExpr {i} (def f (x ∷ [])) | no ¬p | yes p | m = typeError (strErr "not enough args to plus" ∷ [])
toExpr {i} (def f (arg i₁ x ∷ arg i₂ y ∷ args)) | no ¬p | yes p | m = do
  x′ ← toExpr x
  y′ ← toExpr y
  returnTC (x′ ⊕ y′)
toExpr {i} (def f []) | no ¬p | no ¬p₁ | yes p = typeError (strErr "not enough args to mult" ∷ [])
toExpr {i} (def f (x ∷ [])) | no ¬p | no ¬p₁ | yes p = typeError (strErr "not enough args to mult" ∷ [])
toExpr {i} (def f (arg i₁ x ∷ arg i₂ y ∷ args)) | no ¬p | no ¬p₁ | yes p = do
  x′ ← toExpr x
  y′ ← toExpr y
  returnTC (x′ ⊗ y′)
toExpr {i} (def f args) | no ¬p | no ¬p₁ | no ¬p₂ = ringLiteral (def f args)

macro
  genExpr : Term → Term → TC ⊤
  genExpr expr hole = do
    expr′ ← toExpr {zero} expr >>= quoteTC
    unify hole expr′

module Example where
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  ex₁ : genExpr (1# + 0#) ≡ Κ 1# ⊕ Κ 0#
  ex₁ = ≡.refl


nlam : ℕ → Term → Term
nlam zero x = x
nlam (suc i) x = lam visible (abs "a" (nlam i x))

solveGoal : Term → TC Term
solveGoal = go 0
  where
  go : ℕ → Term → TC Term
  go i (def f (arg i₁ x ∷ arg i₂ y ∷ args)) = do
    cnt ← getContext
    x′ ← inContext cnt (toExpr {i} x >>= quoteTC)
    y′ ← inContext cnt (toExpr {i} y >>= quoteTC)
    i′ ← quoteTC i
    returnTC (def (quote solve) (arg (arg-info visible relevant) i′
             ∷ arg (arg-info visible relevant) (nlam i (def (quote _⊜_) (arg (arg-info visible relevant) x′ ∷ arg (arg-info visible relevant) y′ ∷ [])))
             ∷ arg (arg-info visible relevant) (def (quote refl) [])
             ∷ []))
  -- go i t@(def f (arg i₁ x ∷ arg i₂ y ∷ args)) | no ¬p = typeError (strErr "expected lambda or equation, found def" ∷ nameErr f ∷ termErr t ∷ [])
  go i (pi a (abs s x)) =  go (suc i) x
  go i (lam _ (abs s x)) = go i x
  go i t@(var x args) =  typeError (strErr "expected lambda or equation, found var" ∷ termErr t ∷ [])
  go i t@(con c args) =  typeError (strErr "expected lambda or equation, found con" ∷ termErr t ∷ [])
  go i t@(def f args) =  typeError (strErr "expected lambda or equation, found def with too few args" ∷ termErr t ∷ [])
  go i t@(pat-lam cs args) =  typeError (strErr "expected lambda or equation, found pat-lam" ∷ termErr t ∷ [])
  go i t@(sort s) =  typeError (strErr "expected lambda or equation, found sort" ∷ termErr t ∷ [])
  go i t@(lit l) =  typeError (strErr "expected lambda or equation, found lit" ∷ termErr t ∷ [])
  go i t@(meta x x₁) =  typeError (strErr "expected lambda or equation, found meta" ∷ termErr t ∷ [])
  go i t@unknown =  typeError (strErr "expected lambda or equation, found unknown" ∷ termErr t ∷ [])

macro
  autosolve : Term → TC ⊤
  autosolve hole = do
    goal ← inferType hole
    proof ← solveGoal goal
    unify hole proof

-- module Examples where
--   open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
--   open import Function

--   ex₁ : genExpr (1# * 0#) ≡ Κ 1# ⊗ Κ 0#
--   ex₁ = ≡.refl
