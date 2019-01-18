{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters
open import Algebra

module Polynomial.NormalForm.Operations
  {a}
  (coeffs : RawCoeff a)
  where

open import Polynomial.Exponentiation (RawCoeff.coeffs coeffs)

open import Data.Nat as ℕ          using (ℕ; suc; zero)
open import FastCompare            using (compare)
open import Data.Nat.Properties    using (z≤′n)
open import Data.List              using (_∷_; [])
open import Data.Fin               using (Fin)
open import Data.Product           using (_,_; map₁)
open import Induction.WellFounded  using (Acc; acc)
open import Induction.Nat          using (<′-wellFounded)

open import Polynomial.NormalForm.InjectionIndex
open import Polynomial.NormalForm.Definition coeffs
open import Polynomial.NormalForm.Construction coeffs

open RawCoeff coeffs

----------------------------------------------------------------------
-- Addition
----------------------------------------------------------------------
-- The reason the following code is so verbose is termination
-- checking. For instance, in the third case for ⊞-coeffs, we call a
-- helper function. Instead, you could conceivably use a with-block
-- (on ℕ.compare p q):
--
-- ⊞-coeffs ((x , p) ∷ xs) ((y , q) ∷ ys) with (ℕ.compare p q)
-- ... | ℕ.less    p k = (x , p) ∷ ⊞-coeffs xs ((y , k) ∷ ys)
-- ... | ℕ.equal   p   = (fst~ x ⊞ fst~ y , p) ∷↓ ⊞-coeffs xs ys
-- ... | ℕ.greater q k = (y , q) ∷ ⊞-coeffs ((x , k) ∷ xs) ys
--
-- However, because the first and third recursive calls each rewrap
-- a list that was already pattern-matched on, the recursive call
-- does not strictly decrease the size of its argument.
--
-- Interestingly, if --without-K is turned off, we don't need the
-- helper function ⊞-coeffs; we could pattern match on _⊞_ directly.
--
-- _⊞_ {zero} (lift x) (lift y) = lift (x + y)
-- _⊞_ {suc n} [] ys = ys
-- _⊞_ {suc n} (x ∷ xs) [] = x ∷ xs
-- _⊞_ {suc n} ((x , p) ∷ xs) ((y , q) ∷ ys) =
--   ⊞-zip (ℕ.compare p q) x xs y ys

infixl 6 _⊞_
_⊞_ : ∀ {n} → Poly n → Poly n → Poly n

⊞-match : ∀ {i j n}
      → {i≤n : i ≤′ n}
      → {j≤n : j ≤′ n}
      → InjectionOrdering i≤n j≤n
      → FlatPoly i
      → FlatPoly j
      → Poly n

⊞-inj : ∀ {i k}
      → (i ≤′ k)
      → FlatPoly i
      → Coeffs k
      → Coeffs k

⊞-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n

⊞-zip : ∀ {p q n}
      → ℕ.Ordering p q
      → NonZero n
      → Coeffs n
      → NonZero n
      → Coeffs n
      → Coeffs n

⊞-zip-r : ∀ {n} → NonZero n → ℕ → Coeffs n → Coeffs n → Coeffs n

(xs Π i≤n) ⊞ (ys Π j≤n) = ⊞-match (inj-compare i≤n j≤n) xs ys

⊞-match (inj-eq i&j≤n)     (Κ x)  (Κ y)  = Κ (x + y)         Π  i&j≤n
⊞-match (inj-eq i&j≤n)     (Σ xs) (Σ ys) = ⊞-coeffs    xs ys Π↓ i&j≤n
⊞-match (inj-lt i≤j-1 j≤n)  xs    (Σ ys) = ⊞-inj i≤j-1 xs ys Π↓ j≤n
⊞-match (inj-gt i≤n j≤i-1) (Σ xs)  ys    = ⊞-inj j≤i-1 ys xs Π↓ i≤n

⊞-inj i≤k xs [] = xs Π i≤k Δ zero ∷↓ []
⊞-inj i≤k xs (y Π j≤k ≠0 Δ zero ∷ ys) = ⊞-match (inj-compare j≤k i≤k) y xs Δ zero ∷↓ ys
⊞-inj i≤k xs (y Δ suc j ∷ ys) = xs Π i≤k Δ zero ∷↓ y Δ j ∷ ys

⊞-coeffs [] ys = ys
⊞-coeffs (x Δ i ∷ xs) ys = ⊞-zip-r x i xs ys

⊞-zip (ℕ.less    i k) x xs y ys = x Δ i ∷ ⊞-zip-r y k ys xs
⊞-zip (ℕ.greater j k) x xs y ys = y Δ j ∷ ⊞-zip-r x k xs ys
⊞-zip (ℕ.equal   i  ) x xs y ys = (x .poly ⊞ y .poly) Δ i ∷↓ ⊞-coeffs xs ys
{-# INLINE ⊞-zip #-}

⊞-zip-r x i xs [] = x Δ i ∷ xs
⊞-zip-r x i xs (y ∷ ys) = ⊞-zip (compare i (y .pow)) x xs (y .coeff) ys

----------------------------------------------------------------------
-- Negation
----------------------------------------------------------------------

-- recurse on acc directly
-- https://github.com/agda/agda/issues/3190#issuecomment-416900716

⊟-step : ∀ {n} → Acc _<′_ n → Poly n → Poly n
⊟-step _        (Κ x  Π i≤n) = Κ (- x) Π i≤n
⊟-step (acc wf) (Σ xs Π i≤n) = poly-map (⊟-step (wf _ i≤n)) xs Π↓ i≤n

⊟_ : ∀ {n} → Poly n → Poly n
⊟_ = ⊟-step (<′-wellFounded _)
{-# INLINE ⊟_ #-}

----------------------------------------------------------------------
-- Multiplication
----------------------------------------------------------------------
⊠-step : ∀ {i n} → Acc _<′_ n → FlatPoly i → i ≤′ n → Poly n → Poly n

⊠-Κ : ∀ {n} → Acc _<′_ n → Carrier → Poly n → Poly n

⊠-Σ : ∀ {i n} → Acc _<′_ n → Coeffs i → i <′ n → Poly n → Poly n

⊠-Κ-inj : ∀ {i}  → Acc _<′_ i → Carrier → Coeffs i → Coeffs i

⊠-Σ-inj : ∀ {i k}
        → Acc _<′_ k
        → i <′ k
        → Coeffs i
        → Poly k
        → Poly k

⊠-match : ∀ {i j n}
        → Acc _<′_ n
        → {i≤n : i <′ n}
        → {j≤n : j <′ n}
        → InjectionOrdering i≤n j≤n
        → Coeffs i
        → Coeffs j
        → Poly n

⊠-coeffs : ∀ {n} → Acc _<′_ n → Coeffs n → Coeffs n → Coeffs n

⊠-cons : ∀ {n}
        → Acc _<′_ n
        → Poly n
        → Coeffs n
        → Fold n

⊠-step a (Κ x) _ = ⊠-Κ a x
⊠-step a (Σ xs)  = ⊠-Σ a xs

⊠-Κ (acc _ ) x (Κ y  Π i≤n) = Κ (x * y) Π i≤n
⊠-Κ (acc wf) x (Σ xs Π i≤n) = ⊠-Κ-inj (wf _ i≤n) x xs Π↓ i≤n
{-# INLINE ⊠-Κ #-}

⊠-Σ a xs i≤n (Σ ys Π j≤n) = ⊠-match a (inj-compare i≤n j≤n) xs ys
⊠-Σ (acc wf) xs i≤n (Κ y Π _) = ⊠-Κ-inj (wf _ i≤n) y xs Π↓ i≤n
⊠-Κ-inj a x = poly-map (⊠-Κ a x)
⊠-Σ-inj a i≤k x (Σ y Π j≤k) = ⊠-match a (inj-compare i≤k j≤k) x y
⊠-Σ-inj (acc wf) i≤k x (Κ y Π j≤k) = ⊠-Κ-inj (wf _ i≤k) y x Π↓ i≤k
⊠-match (acc wf) (inj-eq i&j≤n)     xs ys = ⊠-coeffs (wf _ i&j≤n) xs ys               Π↓ i&j≤n
⊠-match (acc wf) (inj-lt i≤j-1 j≤n) xs ys = poly-map (⊠-Σ-inj (wf _ j≤n) i≤j-1 xs) ys Π↓ j≤n
⊠-match (acc wf) (inj-gt i≤n j≤i-1) xs ys = poly-map (⊠-Σ-inj (wf _ i≤n) j≤i-1 ys) xs Π↓ i≤n
⊠-coeffs _ _ [] = []
⊠-coeffs a xs (y ≠0 Δ j ∷ ys) = para (⊠-cons a y ys) xs ⍓ j
⊠-cons a y ys (x Π j≤n , xs) =
  ⊠-step a x j≤n y , ⊞-coeffs (poly-map (⊠-step a x j≤n) ys) xs

infixl 7 _⊠_
_⊠_ : ∀ {n} → Poly n → Poly n → Poly n
_⊠_ (x Π i≤n) = ⊠-step (<′-wellFounded _) x i≤n
{-# INLINE _⊠_ #-}

----------------------------------------------------------------------
-- Constants and Variables
----------------------------------------------------------------------

-- The constant polynomial
κ : ∀ {n} → Carrier → Poly n
κ x = Κ x Π z≤′n
{-# INLINE κ #-}

-- A variable
ι : ∀ {n} → Fin n → Poly n
ι i = (κ 1# Δ 1 ∷↓ []) Π↓ Fin⇒≤ i
{-# INLINE ι #-}

----------------------------------------------------------------------
-- Exponentiation
----------------------------------------------------------------------
⊡-mult : ∀ {n} → ℕ → Poly n → Poly n
⊡-mult zero xs = xs
⊡-mult (suc n) xs = xs ⊠ ⊡-mult n xs

infixr 8 _⊡_
_⊡_ : ∀ {n} → Poly n → ℕ → Poly n
_ ⊡ zero = κ 1#
xs@(Κ x Π i≤n) ⊡ suc i = Κ (x ^ i +1) Π i≤n
(Σ [] {()} Π i≤n) ⊡ suc i
(Σ (x Δ j ∷ []) Π i≤n) ⊡ suc i = x .poly ⊡ suc i Δ (i ℕ.* j) ∷↓ [] Π↓ i≤n
xs@(Σ (_ ∷ _ ∷ _) Π _) ⊡ suc i = ⊡-mult i xs
{-# INLINE _⊡_ #-}
