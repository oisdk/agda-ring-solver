{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters

module Polynomial.NormalForm.Construction
  {a}
  (coeffs : RawCoeff a)
  where

open import Relation.Nullary         using (Dec; yes; no)
open import Level                    using (lift; lower; _⊔_)
open import Data.Unit                using (tt)
open import Data.List                using (_∷_; []; List; foldr)
open import Data.Nat            as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties      using (z≤′n)
open import Data.Product             using (_×_; _,_; map₁; curry; uncurry)
open import Data.Maybe               using (just; nothing)
open import Data.Bool                using (if_then_else_; true; false)

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
zero? (Σ _ Π _) = no (λ z → z)
zero? (Κ x Π _) with Zero-C x
... | true = yes tt
... | false = no (λ z → z)
{-# INLINE zero? #-}

-- Exponentiate the first variable of a polynomial
infixr 8 _⍓_ _[⍓]_
_⍓_ : ∀ {n} → [Coeffs] n → ℕ → [Coeffs] n
_[⍓]_ : ∀ {n} → Coeffs n → ℕ → Coeffs n

[] ⍓ _ = []
[ xs ] ⍓ i = [ xs [⍓] i ]

coeff (head (xs [⍓] i)) = coeff (head xs)
pow (head (xs [⍓] i)) = pow (head xs) ℕ.+ i
tail (xs [⍓] i) = tail xs

infixr 5 _∷↓_
_∷↓_ : ∀ {n} → PowInd (Poly n) → [Coeffs] n → [Coeffs] n
x Δ i ∷↓ xs = case zero? x of
  λ { (yes p) → xs ⍓ suc i
    ; (no ¬p) → [ _≠0 x {¬p} Δ i & xs ]
    }
{-# INLINE _∷↓_ #-}

-- Inject a polynomial into a larger polynomoial with more variables
_Π↑_ : ∀ {n m} → Poly n → (suc n ≤′ m) → Poly m
(xs Π i≤n) Π↑ n≤m = xs Π (≤′-step i≤n ⟨ ≤′-trans ⟩ n≤m)
{-# INLINE _Π↑_ #-}

infixr 4 _Π↓_
_Π↓_ : ∀ {i n} → [Coeffs] i → suc i ≤′ n → Poly n
[]                       Π↓ i≤n = Κ 0# Π z≤′n
[ x ≠0 Δ zero  & [] ]      Π↓ i≤n = x Π↑ i≤n
[ x    Δ zero  & [ xs ] ] Π↓ i≤n = Σ (x Δ zero  & [ xs ]) Π i≤n
[ x    Δ suc j & xs ]      Π↓ i≤n = Σ (x  Δ suc j & xs) Π i≤n
{-# INLINE _Π↓_ #-}

--------------------------------------------------------------------------------
-- These folds allow us to abstract over the proofs later: we try to avoid
-- using ∷↓ and Π↓ directly anywhere except here, so if we prove that this fold
-- acts the same on a normalised or non-normalised polynomial, we can prove th
-- same about any operation which uses it.
PolyF : ℕ → Set a
PolyF i = Poly i × [Coeffs] i

Fold : ℕ → Set a
Fold i = PolyF i → PolyF i

para : ∀ {i} → Fold i → Coeffs i → [Coeffs] i
para f (x ≠0 Δ i & []) = case f (x , []) of λ { (y , ys) → y Δ i ∷↓ ys }
para f (x ≠0 Δ i & [ xs ]) = case f (x , para f xs) of λ { (y , ys) → y Δ i ∷↓ ys }

poly-map : ∀ {i} → (Poly i → Poly i) → Coeffs i → [Coeffs] i
poly-map f = para (λ { (x , y) → (f x , y)})
{-# INLINE poly-map #-}
