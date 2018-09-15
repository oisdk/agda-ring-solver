{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary
open import Relation.Nullary
open import Algebra.Solver.Ring.AlmostCommutativeRing

module Polynomials.Ring.Reflection
  {ℓ₁ ℓ₂}
  (ring : AlmostCommutativeRing ℓ₁ ℓ₂)
  (_≈?_ : Decidable (AlmostCommutativeRing._≈_ ring))
  where

open import Reflection
open AlmostCommutativeRing ring hiding (zero)
open import Data.Maybe
open import Polynomials.Ring.FlatExpr

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Fin as Fin
open import Data.List hiding (fromMaybe)
open import Data.Unit
open import Data.Maybe
open import Category.Monad
open import Function
import Level
open import Data.Product
open import Polynomials.Ring.Expr rawRing (_≈ 0#) (λ x → x ≈? 0#) ring (-raw-almostCommutative⟶ ring) (λ x z → z) using (solve) public

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

  open TCMonad

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


  plusExpr : ℕ → Term → Term → Term
  plusExpr i x y = con (quote _⊕_) (i exprCon visible-arg x ∷ visible-arg y ∷ [])

  multExpr : ℕ → Term → Term → Term
  multExpr i x y = con (quote _⊗_) (i exprCon visible-arg x ∷ visible-arg y ∷ [])

  negExpr : ℕ → Term → Term
  negExpr i x = con (quote ⊝_) (i exprCon visible-arg x ∷ [])

  varExpr : (i : ℕ) → Fin.Fin i → Term
  varExpr i x = con (quote Ι) (i exprCon visible-arg (finTerm x) ∷ [])

  constExpr : ℕ → Term → Term
  constExpr i x = con (quote Κ) (i exprCon visible-arg x ∷ [])

  revFin : ∀ {x y} → suc x ℕ.≤ y → Fin.Fin y
  revFin {x} {y} prf = Fin.fromℕ≤ (NP.≤″⇒≤ prf₂)
    where
    import Data.Nat.Properties as NP
    import Relation.Binary.PropositionalEquality as ≡
    prf₁ : suc x ℕ.≤″ y
    prf₁ = NP.≤⇒≤″ prf
    prf₂ : suc (ℕ._≤″_.k prf₁) ℕ.≤″ y
    prf₂ = ℕ.less-than-or-equal (≡.trans (≡.cong suc (NP.+-comm _ x)) (ℕ._≤″_.proof prf₁))



  toExpr : (i : ℕ) → Term → Term
  toExpr i (def f (_ ∷ _ ∷ _ ∷ visible-arg x ∷ visible-arg y ∷  _)) with f ≟-Name quote AlmostCommutativeRing._+_
  toExpr i (def f (_ ∷ _ ∷ _ ∷ visible-arg x ∷ visible-arg y ∷ _)) | yes p = plusExpr i (toExpr i x) (toExpr i y)
  toExpr i (def f (_ ∷ _ ∷ _ ∷ visible-arg x ∷ visible-arg y ∷ _)) | no ¬p with f ≟-Name quote AlmostCommutativeRing._*_
  toExpr i (def f (_ ∷ _ ∷ _ ∷ visible-arg x ∷ visible-arg y ∷ _)) | no ¬p | yes p = multExpr i (toExpr i x) (toExpr i y)
  toExpr i t@(def f (_ ∷ _ ∷ _ ∷ visible-arg x ∷ visible-arg y ∷ _)) | no ¬p | no ¬p₁ = constExpr i t
  toExpr i (def f (_ ∷ _ ∷ _ ∷ visible-arg x ∷ _)) with f ≟-Name quote AlmostCommutativeRing.-_
  toExpr i (def f (_ ∷ _ ∷ _ ∷ visible-arg x ∷ _)) | yes p = negExpr i (toExpr i x)
  toExpr i t@(def f (_ ∷ _ ∷ _ ∷ visible-arg x ∷ _)) | no ¬p = negExpr i t
  toExpr i (var x args) with suc x ℕ.≤? i
  toExpr i (var x args) | yes p = varExpr i (revFin p)
  toExpr i t@(var x args) | no ¬p = constExpr i t
  toExpr i t = constExpr i t

  macro
    qExpr : Term → Term → TC ⊤
    qExpr expr hole = unify hole (toExpr 0 expr)

  toEquiv : Term → Term
  toEquiv = go 0
    where
    go : ℕ → Term → Term
    go i (def f (_ ∷ _ ∷ _ ∷ visible-arg lhs ∷ visible-arg rhs ∷ _)) = con (quote _,_) (hidden-arg unknown ∷ hidden-arg unknown ∷ hidden-arg unknown ∷ hidden-arg unknown ∷ visible-arg (toExpr i lhs) ∷ visible-arg (toExpr i rhs) ∷ [])
    go i (pi a (abs s x)) = lam visible (abs s (go (suc i) x))
    go i _ = unknown

open Internal
macro
  makeGoal : Term → Term → TC ⊤
  makeGoal expr hole = unify hole (toEquiv expr)
