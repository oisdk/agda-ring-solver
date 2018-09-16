module Polynomials.Ring.Simple.Reflection where

open import Reflection
open import Data.Maybe
open import Polynomials.Ring.Expr
open import Polynomials.Ring.Simple.AlmostCommutativeRing
open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Fin as Fin
open import Data.List hiding (fromMaybe)
open import Data.Unit
open import Data.Maybe
open import Category.Monad
open import Function
import Level
open import Data.Product

module Internal where
  module TCMonad where
    infixl 1 _>>=_ _>>_ _>=>_
    _>>=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
    _>>=_ = bindTC

    _>>_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → TC B → TC B
    xs >> ys = do
      x ← xs
      ys

    _>=>_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (A → TC B) → (B → TC C) → A → TC C
    _>=>_ fs gs x = fs x >>= gs

    return : ∀ {a} {A : Set a} → A → TC A
    return = returnTC

    infixl 4 _<$>_ _<*>_
    _<$>_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → TC A → TC B
    f <$> xs = do
      x ← xs
      return (f x)

    _<*>_ : ∀ {a b} → {A : Set a} {B : Set b} → TC (A → B) → TC A → TC B
    fs <*> xs = do
      f ← fs
      x ← xs
      return (f x)

  open TCMonad public

  pattern hidden-arg x = arg (arg-info hidden relevant) x
  pattern visible-arg x = arg (arg-info visible relevant) x

  natTerm : ℕ → Term
  natTerm zero = con (quote zero) []
  natTerm (suc i) = con (quote suc) (visible-arg (natTerm i) ∷ [])

  finTerm : ∀ {i} → Fin.Fin i → Term
  finTerm {suc i} Fin.zero = con (quote Fin.zero) (hidden-arg (natTerm i) ∷ [])
  finTerm {suc i} (Fin.suc x) = con (quote Fin.suc) (hidden-arg (natTerm i) ∷ visible-arg (finTerm x) ∷ [])

  infixr 5 _exprCon_
  _exprCon_ : ℕ → List (Arg Term) → List (Arg Term)
  i exprCon xs = hidden-arg unknown ∷ hidden-arg unknown ∷ hidden-arg (natTerm i) ∷ xs

  constExpr : ℕ → Term → Term
  constExpr i x = con (quote Κ) (i exprCon visible-arg x ∷ [])


  mutual
    getBinOp : ℕ → Name → List (Arg Term) → Term
    getBinOp i nm (visible-arg x ∷ visible-arg y ∷ []) = con nm (i exprCon visible-arg (toExpr i x) ∷ visible-arg (toExpr i y) ∷ [])
    getBinOp i nm (x ∷ xs) = getBinOp i nm xs
    getBinOp _ _ _ = unknown

    getUnOp : ℕ → Name → List (Arg Term) → Term
    getUnOp i nm (visible-arg x ∷ []) = con nm (i exprCon visible-arg (toExpr i x) ∷ [])
    getUnOp _ _ _ = unknown

    toExpr : (i : ℕ) → Term → Term
    toExpr i t@(def f xs) with f ≟-Name quote AlmostCommutativeRing._+_
    ... | yes p = getBinOp i (quote _⊕_) xs
    ... | no _ with f ≟-Name quote AlmostCommutativeRing._*_
    ... | yes p = getBinOp i (quote _⊗_) xs
    ... | no _ with f ≟-Name quote AlmostCommutativeRing.-_
    ... | yes p = getUnOp i (quote ⊝_) xs
    ... | no _ = constExpr i t
    toExpr i (var x args) with suc x ℕ.≤? i
    toExpr i v@(var x args) | yes p = v
    toExpr i t@(var x args) | no ¬p = constExpr i t
    toExpr i t = constExpr i t

  macro
    qExpr : Term → Term → TC ⊤
    qExpr expr hole = unify hole (toExpr 0 expr)

  open import Polynomials.Ring.Simple.Solver renaming (solve to solve′)

  open import Data.String

  hlams : List String → Term → Term
  hlams [] xs = xs
  hlams (v ∷ vs) xs = lam hidden (abs v (hlams vs xs))

  vlams : List String → Term → Term
  vlams [] xs = xs
  vlams (v ∷ vs) xs = lam visible (abs v (vlams vs xs))

  mkSolver : List String → Name → ℕ → Term → Term → Term
  mkSolver nms rng i lhs rhs = def (quote solve′)
    ( hidden-arg unknown
    ∷ hidden-arg unknown
    ∷ visible-arg (def rng [])
    ∷ visible-arg (natTerm i)
    ∷ visible-arg (vlams nms (def (quote _⊜_) (hidden-arg unknown ∷ hidden-arg unknown ∷ visible-arg (def rng []) ∷ (visible-arg (natTerm i)) ∷ visible-arg (toExpr i lhs) ∷ visible-arg (toExpr i rhs) ∷ [])))
    ∷ visible-arg (hlams nms (def (quote AlmostCommutativeRing.refl) (hidden-arg unknown ∷ hidden-arg unknown ∷ visible-arg (def rng []) ∷ hidden-arg unknown ∷ [])))
    ∷ [])


  toSoln : Name → Term → Term
  toSoln rng = go 0 id
    where
    go : ℕ → (List String → List String) → Term → Term
    go i k (def f (visible-arg lhs ∷ visible-arg rhs ∷ [])) = mkSolver (k []) rng i lhs rhs
    go i k (def f (_ ∷ _ ∷ visible-arg lhs ∷ visible-arg rhs ∷ [])) = mkSolver (k []) rng i lhs rhs
    go i k (def f (_ ∷ _ ∷ _ ∷ visible-arg lhs ∷ visible-arg rhs ∷ [])) = mkSolver (k []) rng i lhs rhs
    go i k (pi a (abs s x)) = go (suc i) (k ∘ (s ∷_)) x
    go i k t = unknown

open Internal
open import Agda.Builtin.Reflection
macro
  solve : Name → Term → TC ⊤
  solve rng hole = do
    goal ← inferType hole >>= reduce
    unify (toSoln rng goal) hole
