{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters
open import Algebra

module Polynomial.NormalForm.Operations
  {a}
  (coeffs : RawCoeff a)
  where

open import Polynomial.Exponentiation (RawCoeff.coeffs coeffs)

open import Data.Nat as ℕ          using (ℕ; suc; zero; compare)
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
mutual
  infixl 6 _⊞_
  _⊞_ : ∀ {n} → Poly n → Poly n → Poly n
  (xs Π i≤n) ⊞ (ys Π j≤n) = ⊞-match (inj-compare i≤n j≤n) xs ys

  ⊞-match : ∀ {i j n}
        → {i≤n : i ≤′ n}
        → {j≤n : j ≤′ n}
        → InjectionOrdering i≤n j≤n
        → FlatPoly i
        → FlatPoly j
        → Poly n
  ⊞-match (inj-eq i&j≤n)     (Κ x)  (Κ y)  = Κ (x + y)         Π  i&j≤n
  ⊞-match (inj-eq i&j≤n)     (Σ (x Δ i & xs)) (Σ (y Δ j & ys)) = ⊞-zip (compare i j) x xs y ys Π↓ i&j≤n
  ⊞-match (inj-lt i≤j-1 j≤n)  xs    (Σ ys) = ⊞-inj i≤j-1 xs ys Π↓ j≤n
  ⊞-match (inj-gt i≤n j≤i-1) (Σ xs)  ys    = ⊞-inj j≤i-1 ys xs Π↓ i≤n

  ⊞-inj : ∀ {i k}
        → (i ≤′ k)
        → FlatPoly i
        → Coeff k ⁺
        → Coeff k ⋆
  ⊞-inj i≤k xs (y Π j≤k ≠0 Δ zero & ys) = ⊞-match (inj-compare j≤k i≤k) y xs Δ zero ∷↓ ys
  ⊞-inj i≤k xs (y Δ suc j & ys) = xs Π i≤k Δ zero ∷↓ [ y Δ j & ys ]

  ⊞-coeffs : ∀ {n} → Coeff n ⋆ → Coeff n ⋆ → Coeff n ⋆
  ⊞-coeffs [ x Δ i & xs ] ys = ⊞-zip-r x i xs ys
  ⊞-coeffs [] ys = ys

  ⊞-zip : ∀ {p q n}
        → ℕ.Ordering p q
        → NonZero n
        → Coeff n ⋆
        → NonZero n
        → Coeff n ⋆
        → Coeff n ⋆
  ⊞-zip (ℕ.less    i k) x xs y ys = [ x Δ i & ⊞-zip-r y k ys xs ]
  ⊞-zip (ℕ.greater j k) x xs y ys = [ y Δ j & ⊞-zip-r x k xs ys ]
  ⊞-zip (ℕ.equal   i  ) x xs y ys = (x .poly ⊞ y .poly) Δ i ∷↓ ⊞-coeffs xs ys

  ⊞-zip-r : ∀ {n} → NonZero n → ℕ → Coeff n ⋆ → Coeff n ⋆ → Coeff n ⋆
  ⊞-zip-r x i xs [] = [ x Δ i & xs ]
  ⊞-zip-r x i xs [ y Δ j & ys ] = ⊞-zip (compare i j) x xs y ys
{-# INLINE ⊞-zip #-}

----------------------------------------------------------------------
-- Negation
----------------------------------------------------------------------

-- recurse on acc directly
-- https://github.com/agda/agda/issues/3190#issuecomment-416900716

⊟-step : ∀ {n} → Acc _<′_ n → Poly n → Poly n
⊟-step (acc wf) (Κ x  Π i≤n) = Κ (- x) Π i≤n
⊟-step (acc wf) (Σ xs Π i≤n) = poly-map (⊟-step (wf _ i≤n)) xs Π↓ i≤n

⊟_ : ∀ {n} → Poly n → Poly n
⊟_ = ⊟-step (<′-wellFounded _)
{-# INLINE ⊟_ #-}

----------------------------------------------------------------------
-- Multiplication
----------------------------------------------------------------------
mutual
  ⊠-step′ : ∀ {n} → Acc _<′_ n → Poly n → Poly n → Poly n
  ⊠-step′ a (x Π i≤n) = ⊠-step a x i≤n

  ⊠-step : ∀ {i n} → Acc _<′_ n → FlatPoly i → i ≤′ n → Poly n → Poly n
  ⊠-step a (Κ x) _ = ⊠-Κ a x
  ⊠-step a (Σ xs)  = ⊠-Σ a xs

  ⊠-Κ : ∀ {n} → Acc _<′_ n → Carrier → Poly n → Poly n
  ⊠-Κ (acc _ ) x (Κ y  Π i≤n) = Κ (x * y) Π i≤n
  ⊠-Κ (acc wf) x (Σ xs Π i≤n) = ⊠-Κ-inj (wf _ i≤n) x xs Π↓ i≤n

  ⊠-Σ : ∀ {i n} → Acc _<′_ n → Coeff i ⁺ → i <′ n → Poly n → Poly n
  ⊠-Σ (acc wf) xs i≤n (Σ ys Π j≤n) = ⊠-match  (acc wf) (inj-compare i≤n j≤n) xs ys
  ⊠-Σ (acc wf) xs i≤n (Κ y Π _) = ⊠-Κ-inj (wf _ i≤n) y xs Π↓ i≤n

  ⊠-Κ-inj : ∀ {i}  → Acc _<′_ i → Carrier → Coeff i ⁺ → Coeff i ⋆
  ⊠-Κ-inj a x xs = poly-map (⊠-Κ a x) (xs)

  ⊠-Σ-inj : ∀ {i k}
          → Acc _<′_ k
          → i <′ k
          → Coeff i ⁺
          → Poly k
          → Poly k
  ⊠-Σ-inj (acc wf) i≤k x (Σ y Π j≤k) = ⊠-match (acc wf) (inj-compare i≤k j≤k) x y
  ⊠-Σ-inj (acc wf) i≤k x (Κ y Π j≤k) = ⊠-Κ-inj (wf _ i≤k) y x Π↓ i≤k

  ⊠-match : ∀ {i j n}
          → Acc _<′_ n
          → {i≤n : i <′ n}
          → {j≤n : j <′ n}
          → InjectionOrdering i≤n j≤n
          → Coeff i ⁺
          → Coeff j ⁺
          → Poly n
  ⊠-match (acc wf) (inj-eq i&j≤n)     xs ys = ⊠-coeffs (wf _ i&j≤n) xs ys               Π↓ i&j≤n
  ⊠-match (acc wf) (inj-lt i≤j-1 j≤n) xs ys = poly-map (⊠-Σ-inj (wf _ j≤n) i≤j-1 xs) (ys) Π↓ j≤n
  ⊠-match (acc wf) (inj-gt i≤n j≤i-1) xs ys = poly-map (⊠-Σ-inj (wf _ i≤n) j≤i-1 ys) (xs) Π↓ i≤n

  ⊠-coeffs : ∀ {n} → Acc _<′_ n → Coeff n ⁺ → Coeff n ⁺ → Coeff n ⋆
  ⊠-coeffs a (xs) (y ≠0 Δ j & []) = poly-map (⊠-step′ a y) (xs) ⍓ j
  ⊠-coeffs a (xs) (y ≠0 Δ j & [ ys ]) = para (⊠-cons a y ys) (xs) ⍓ j

  ⊠-cons : ∀ {n}
          → Acc _<′_ n
          → Poly n
          → Coeff n ⁺
          → Fold n
  -- ⊠-cons a y [] (x Π j≤n , xs) = ⊠-step a x j≤n y , xs
  ⊠-cons a y ys (x Π j≤n , xs) =
    ⊠-step a x j≤n y , ⊞-coeffs (poly-map (⊠-step a x j≤n) ys) xs
{-# INLINE ⊠-Κ #-}
{-# INLINE ⊠-coeffs #-}
{-# INLINE ⊠-cons #-}

infixl 7 _⊠_
_⊠_ : ∀ {n} → Poly n → Poly n → Poly n
_⊠_ = ⊠-step′ (<′-wellFounded _)
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
-- We try very hard to never do things like multiply by 1
-- unnecessarily. That's what all the weirdness here is for.
⊡-mult : ∀ {n} → ℕ → Poly n → Poly n
⊡-mult zero xs = xs
⊡-mult (suc n) xs = ⊡-mult n xs ⊠ xs

_⊡_+1 : ∀ {n} → Poly n → ℕ → Poly n
(Κ x  Π i≤n) ⊡ i +1  = Κ (x ^ i +1) Π i≤n
(Σ (x Δ j & []) Π i≤n) ⊡ i +1  = x .poly ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ [] Π↓ i≤n
xs@(Σ (_ & [ _ ]) Π i≤n) ⊡ i +1  = ⊡-mult i xs

infixr 8 _⊡_
_⊡_ : ∀ {n} → Poly n → ℕ → Poly n
_ ⊡ zero = κ 1#
xs ⊡ suc i = xs ⊡ i +1
{-# INLINE _⊡_ #-}
