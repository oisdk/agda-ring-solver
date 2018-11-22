{-# OPTIONS --without-K #-}

open import Algebra
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Relation.Binary hiding (Decidable)
open import Relation.Nullary
open import Relation.Unary
open import Level using (_⊔_; Lift; lift; lower)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.List as List using (_∷_; []; List; foldr)
open import Data.Vec as Vec using (_∷_; []; Vec)
open import Data.Nat as ℕ using (ℕ; suc; zero; compare)
open import Function
open import Data.Fin as Fin using (Fin)
open import Polynomial.Parameters
import Data.Nat.Properties as ℕ-Prop

-- Multivariate polynomials.
module Polynomial.NormalForm.Operations
  {a ℓ}
  (coeffs : RawCoeff a ℓ)
  where

open import Polynomial.NormalForm.Definition coeffs
open import Polynomial.NormalForm.Construction coeffs
open RawCoeff coeffs
open import Data.Product

open import Polynomial.NormalForm.InjectionIndex
----------------------------------------------------------------------
-- Gaps
----------------------------------------------------------------------

----------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------


----------------------------------------------------------------------
-- Arithmetic
----------------------------------------------------------------------

----------------------------------------------------------------------
-- Addition
----------------------------------------------------------------------
mutual
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
  (xs Π i≤n) ⊞ (ys Π j≤n) = ⊞-match (i≤n cmp j≤n) xs ys

  ⊞-match : ∀ {i j n}
        → {i≤n : i ≤′ n}
        → {j≤n : j ≤′ n}
        → Ordering i≤n j≤n
        → FlatPoly i
        → FlatPoly j
        → Poly n
  ⊞-match (eq i&j≤n)    (Κ x)  (Κ y)  = Κ (x + y)         Π  i&j≤n
  ⊞-match (eq i&j≤n)    (Σ xs) (Σ ys) = ⊞-coeffs    xs ys Π↓ i&j≤n
  ⊞-match (lt i≤j-1 j≤n)  xs    (Σ ys) = ⊞-inj i≤j-1 xs ys Π↓ j≤n
  ⊞-match (gt i≤n j≤i-1) (Σ xs)  ys    = ⊞-inj j≤i-1 ys xs Π↓ i≤n

  ⊞-inj : ∀ {i k}
       → (i ≤′ k)
       → FlatPoly i
       → Coeffs k
       → Coeffs k
  ⊞-inj i≤k xs [] = xs Π i≤k Δ zero ∷↓ []
  ⊞-inj i≤k xs (y Π j≤k ≠0 Δ zero ∷ ys) =
    ⊞-match (j≤k cmp i≤k) y xs Δ zero ∷↓ ys
  ⊞-inj i≤k xs (y Δ suc j ∷ ys) =
    xs Π i≤k Δ zero ∷↓ y Δ j ∷ ys

  ⊞-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
  ⊞-coeffs [] ys = ys
  ⊞-coeffs (x Δ i ∷ xs) = ⊞-zip-r x i xs

  ⊞-zip : ∀ {p q n}
        → ℕ.Ordering p q
        → NonZero n
        → Coeffs n
        → NonZero n
        → Coeffs n
        → Coeffs n
  ⊞-zip (ℕ.less    i k) x xs y ys = x Δ i ∷ ⊞-zip-r y k ys xs
  ⊞-zip (ℕ.greater j k) x xs y ys = y Δ j ∷ ⊞-zip-r x k xs ys
  ⊞-zip (ℕ.equal   i  ) (x ≠0) xs (y ≠0) ys =
    (x ⊞ y) Δ i ∷↓ ⊞-coeffs xs ys

  ⊞-zip-r : ∀ {n} → NonZero n → ℕ → Coeffs n → Coeffs n → Coeffs n
  ⊞-zip-r x i xs [] = x Δ i ∷ xs
  ⊞-zip-r x i xs (y Δ j ∷ ys) = ⊞-zip (compare i j) x xs y ys

----------------------------------------------------------------------
-- Negation
----------------------------------------------------------------------

open import Induction.WellFounded
open import Induction.Nat

-- recurse on acc directly
-- https://github.com/agda/agda/issues/3190#issuecomment-416900716

mutual
  ⊟-step : ∀ {n} → Acc _<′_ n → Poly n → Poly n
  ⊟-step _        (Κ x  Π i≤n) = Κ (- x) Π i≤n
  ⊟-step (acc wf) (Σ xs Π i≤n) =
    para (⊟-cons (wf _ i≤n)) xs Π↓ i≤n

  ⊟-cons : ∀ {n} → Acc _<′_ n → Fold n
  ⊟-cons ac (x , xs) = ⊟-step ac x , xs

⊟_ : ∀ {n} → Poly n → Poly n
⊟_ = ⊟-step (<′-wellFounded _)

----------------------------------------------------------------------
-- Multiplication
----------------------------------------------------------------------
mutual
  ⊠-step : ∀ {n} → Acc _<′_ n → Poly n → Poly n → Poly n
  ⊠-step a (xs Π i≤n) (ys Π j≤n) = ⊠-match a (i≤n cmp j≤n) xs ys

  ⊠-inj : ∀ {i k}
        → Acc _<′_ k
        → i ≤′ k
        → FlatPoly i
        → Fold k
  ⊠-inj a i≤k x (y Π j≤k , ys) =
    ⊠-match a (i≤k cmp j≤k) x y , ys

  ⊠-match : ∀ {i j n}
          → Acc _<′_ n
          → {i≤n : i ≤′ n}
          → {j≤n : j ≤′ n}
          → Ordering i≤n j≤n
          → FlatPoly i
          → FlatPoly j
          → Poly n
  ⊠-match _ (eq i&j≤n)        (Κ  x) (Κ  y) = Κ (x * y)                           Π  i&j≤n
  ⊠-match (acc wf) (eq i&j≤n) (Σ xs) (Σ ys) = ⊠-coeffs (wf _ i&j≤n) xs ys         Π↓ i&j≤n
  ⊠-match (acc wf) (lt i≤j-1 j≤n) xs (Σ ys)  = para (⊠-inj (wf _ j≤n) i≤j-1 xs) ys Π↓ j≤n
  ⊠-match (acc wf) (gt i≤n j≤i-1) (Σ xs) ys  = para (⊠-inj (wf _ i≤n) j≤i-1 ys) xs Π↓ i≤n

  -- A simple shift-and-add algorithm.
  ⊠-coeffs : ∀ {n} → Acc _<′_ n → Coeffs n → Coeffs n → Coeffs n
  ⊠-coeffs _ _ [] = []
  ⊠-coeffs a xs (y ≠0 Δ j ∷ ys) = para (⊠-cons a y ys) xs ⍓ j

  ⊠-cons : ∀ {n}
         → Acc _<′_ n
         → Poly n
         → Coeffs n
         → Fold n
  ⊠-cons a y ys (x Π j≤n , xs) =
    ⊠-step a (x Π j≤n) y , ⊞-coeffs (para (⊠-inj a j≤n x) ys) xs

infixl 7 _⊠_
_⊠_ : ∀ {n} → Poly n → Poly n → Poly n
_⊠_ = ⊠-step (<′-wellFounded _)

----------------------------------------------------------------------
-- Constants and Variables
----------------------------------------------------------------------

-- The constant polynomial
κ : ∀ {n} → Carrier → Poly n
κ x = Κ x Π ℕ-Prop.z≤′n

-- A variable
ι : ∀ {n} → Fin n → Poly n
ι i = (κ 1# Δ 1 ∷↓ []) Π↓ Fin⇒≤ i
