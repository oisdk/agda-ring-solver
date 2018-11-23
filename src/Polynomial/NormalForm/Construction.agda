{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters

module Polynomial.NormalForm.Construction
  {a ℓ}
  (coeffs : RawCoeff a ℓ)
  where

open import Relation.Nullary         using (Dec; yes; no)
open import Level                    using (lift; lower; _⊔_)
open import Data.Unit                using (tt)
open import Data.List                using (_∷_; []; foldr)
open import Data.Nat            as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties      using (z≤′n)
open import Data.Pair.NonDependent   using (_×_; _,_; map₁; curry; uncurry)

open import Function

open import Polynomial.NormalForm.InjectionIndex
open import Polynomial.NormalForm.Definition coeffs

open RawCoeff coeffs

----------------------------------------------------------------------
-- Construction
--
-- Because the polynomial is stored in a canonical form, we use a
-- normalising cons operator to construct the coefficient lists.
----------------------------------------------------------------------

-- Decision procedure for Zero
zero? : ∀ {n} → (p : Poly n) → Dec (Zero p)
zero? (Κ x       Π _) = zero-c? x
zero? (Σ []      Π _) = yes (lift tt)
zero? (Σ (_ ∷ _) Π _) = no lower

-- Exponentiate the first variable of a polynomial
infixr 8 _⍓_
_⍓_ : ∀ {n} → Coeffs n → ℕ → Coeffs n
[] ⍓ i = []
(x Δ j ∷ xs) ⍓ i = x Δ (j ℕ.+ i) ∷ xs

infixr 5 _∷↓_
_∷↓_ : ∀ {n} → PowInd (Poly n) → Coeffs n → Coeffs n
x Δ i ∷↓ xs with zero? x
... | yes p = xs ⍓ suc i
... | no ¬p = _≠0 x {¬p} Δ i ∷ xs


-- Inject a polynomial into a larger polynomoial with more variables
_Π↑_ : ∀ {n m} → Poly n → (suc n ≤′ m) → Poly m
(xs Π i≤n) Π↑ n≤m = xs Π (≤′-step i≤n ⟨ ≤′-trans ⟩ n≤m)

-- NormalForm.sing Π
infixr 4 _Π↓_
_Π↓_ : ∀ {i n} → Coeffs i → suc i ≤′ n → Poly n
[]                       Π↓ i≤n = Κ 0# Π z≤′n
(x ≠0 Δ zero  ∷ [])      Π↓ i≤n = x Π↑ i≤n
(x₁   Δ zero  ∷ x₂ ∷ xs) Π↓ i≤n = Σ (x₁ Δ zero  ∷ x₂ ∷ xs) Π i≤n
(x    Δ suc j ∷ xs)      Π↓ i≤n = Σ (x  Δ suc j ∷ xs) Π i≤n

PolyF : ℕ → Set (a ⊔ ℓ)
PolyF i = Poly i × Coeffs i

Fold : ℕ → Set (a ⊔ ℓ)
Fold i = PolyF i → PolyF i

para : ∀ {i} → Fold i → Coeffs i → Coeffs i
para f = foldr (λ { (x ≠0 Δ i) → uncurry (_∷↓_ ∘ (_Δ i)) ∘ curry f x}) []

poly-map : ∀ {i} → (Poly i → Poly i) → Coeffs i → Coeffs i
poly-map f = para (map₁ f)
