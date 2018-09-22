{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Nullary
open import Relation.Unary
open import Level using (_⊔_; Lift; lift; lower)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.List as List using (_∷_; []; List; foldr)
open import Data.Vec as Vec using (_∷_; []; Vec)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Function
open import Data.Nat.Order.Gappy

module Polynomials.Ring.Normal.Definition
  {a ℓ}
  (coeffs : RawRing a)
  (Zero-C : Pred (RawRing.Carrier coeffs) ℓ)
  (zero-c? : Decidable Zero-C)
  where

infixl 6 _Δ_
record PowInd {c} (C : Set c) : Set c where
  inductive
  constructor _Δ_
  field
    coeff : C
    pow   : ℕ

module _ where
  open PowInd

  map-coeff : ∀ {c₁ c₂} {C₁ : Set c₁} {C₂ : Set c₂} → (C₁ → C₂) → PowInd C₁ → PowInd C₂
  map-coeff f (x Δ i) = f x Δ i

  map-ind : ∀ {c} {C : Set c} → (ℕ → ℕ) → PowInd C → PowInd C
  map-ind f (x Δ i) = x Δ f i

open RawRing coeffs

mutual
  -- A Polynomial is indexed by the number of variables it contains.
  infixl 6 _Π_
  record Poly (n : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor _Π_
    field
      {i} : ℕ
      flat  : FlatPoly i
      i≤n   : i ≤ n

  -- Possible alternative:
  -- infixl 6 _Σ_
  -- data Poly (n : ℕ) : Set (a ⊔ ℓ) where
  --   Κ   : Carrier → Poly n
  --   _Σ_ : ∀ {i} → suc i ≤ n → (xs : Coeffs i) → .{xn : Norm xs} → Poly n

  data FlatPoly : ℕ → Set (a ⊔ ℓ) where
    Κ : Carrier → FlatPoly 0
    Σ : ∀ {n} → (xs : Coeffs n) → .{xn : Norm xs} → FlatPoly (suc n)

  -- A list of coefficients, paired with the exponent *gap* from the
  -- preceding coefficient. In other words, to represent the
  -- polynomial:
  --
  --   3 + 2x² + 4x⁵ + 2x⁷
  --
  -- We write:
  --
  --   [(3,0),(2,1),(4,2),(2,1)]
  --
  -- Which can be thought of as a representation of the expression:
  --
  --   x⁰ * (3 + x * x¹ * (2 + x * x² * (4 + x * x¹ * (2 + x * 0))))
  --
  -- This is sparse Horner normal form.

  CoeffExp : ℕ → Set (a ⊔ ℓ)
  CoeffExp i = PowInd (Coeff i)

  Coeffs : ℕ → Set (a ⊔ ℓ)
  Coeffs n = List (CoeffExp n)

  -- We disallow zeroes in the coefficient list. This condition alone
  -- is enough to ensure a unique representation for any polynomial.
  infixl 6 _≠0
  record Coeff (i : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor _≠0
    field
      poly : Poly i
      .{poly≠0} : ¬ Zero poly

  Zero : ∀ {n} → Poly n → Set ℓ
  Zero (Κ x       Π _) = Zero-C x
  Zero (Σ []      Π _) = Lift ℓ ⊤
  Zero (Σ (_ ∷ _) Π _) = Lift ℓ ⊥

  Norm : ∀ {i} → Coeffs i → Set
  Norm []                  = ⊥
  Norm (_ Δ zero  ∷ [])    = ⊥
  Norm (_ Δ zero  ∷ _ ∷ _) = ⊤
  Norm (_ Δ suc _ ∷ _)     = ⊤

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

open import Data.Product using (_×_; _,_)

norm-cons : ∀ {n} → PowInd (Poly n) × Coeffs n → Coeffs n
norm-cons (x Δ i , xs) with zero? x
... | yes p = xs ⍓ suc i
... | no ¬p = _≠0 x {¬p} Δ i ∷ xs

un-coeff : ∀ {n} → CoeffExp n → PowInd (Poly n)
un-coeff = map-coeff Coeff.poly

-- Normalising cons
infixr 5 _^_∷↓_
_^_∷↓_ : ∀ {n} → Poly n → ℕ → Coeffs n → Coeffs n
x ^ i ∷↓ xs = norm-cons (x Δ i , xs)

-- Inject a polynomial into a larger polynomoial with more variables
_Π↑_ : ∀ {n m} → Poly n → (suc n ≤ m) → Poly m
(xs Π i≤n) Π↑ n≤m = xs Π (≤-s i≤n ⋈ n≤m)

-- Normalising Π
infixr 4 _Π↓_
_Π↓_ : ∀ {i n} → Coeffs i → suc i ≤ n → Poly n
[]                       Π↓ i≤n = Κ 0# Π z≤n
(x ≠0 Δ zero  ∷ [])      Π↓ i≤n = x Π↑ i≤n
(x₁   Δ zero  ∷ x₂ ∷ xs) Π↓ i≤n = Σ (x₁ Δ zero  ∷ x₂ ∷ xs) Π i≤n
(x    Δ suc j ∷ xs)      Π↓ i≤n = Σ (x  Δ suc j ∷ xs) Π i≤n
