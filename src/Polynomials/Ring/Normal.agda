{-# OPTIONS --without-K #-}

open import Algebra
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Relation.Binary hiding (Decidable)
open import Relation.Nullary
open import Relation.Unary
open import Level using (_⊔_; Lift; lift; lower)
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Data.List as List using (_∷_; []; List)
open import Data.Vec as Vec using (_∷_; []; Vec)
open import Data.Nat as ℕ
  using (ℕ; suc; zero)
open import Data.Product
open import Data.Product.Irrelevant
open import Function
open import Data.Fin as Fin using (Fin)

-- Multivariate polynomials.
module Polynomials.Ring.Normal
  {a ℓ}
  (coeff : RawRing a)
  (Zero-C : Pred (RawRing.Carrier coeff) ℓ)
  (zero-c? : Decidable Zero-C)
  where

open RawRing coeff

----------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------

mutual
  -- A Polynomial is indexed by the number of variables it contains.
  Poly : ℕ → Set (a ⊔ ℓ)
  Poly n = Σ ℕ (NestPoly n)

  infixr 4 _[,]_
  record NestPoly (n i : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor _[,]_
    field
      flat : Σ~ (FlatPoly i) (Norm i)
      i≤n  : i ℕ.≤″ n

  FlatPoly : ℕ → Set (a ⊔ ℓ)
  FlatPoly zero = Lift ℓ Carrier
  FlatPoly (suc n) = Coeffs n

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
  Coeffs : ℕ → Set (a ⊔ ℓ)
  Coeffs n = List (Coeff n × ℕ)

  -- We disallow zeroes in the coefficient list. This condition alone
  -- is enough to ensure a unique representation for any polynomial.
  Coeff : ℕ → Set (a ⊔ ℓ)
  Coeff i = Σ~[ x ∈ Poly i ] ¬ Zero x

  Zero : ∀ {n} → Poly n → Set ℓ
  Zero (zero  , lift x  ,~ _ [,] _) = Zero-C x
  Zero (suc _ , []      ,~ _ [,] _) = Lift ℓ ⊤
  Zero (suc _ , (_ ∷ _) ,~ _ [,] _) = Lift ℓ ⊥

  Norm : ∀ i → FlatPoly i → Set
  Norm zero _ = ⊤
  Norm (suc _) [] = ⊥
  Norm (suc _) ((_ , zero) ∷ []) = ⊥
  Norm (suc _) ((_ , zero) ∷ _ ∷ _) = ⊤
  Norm (suc _) ((_ , suc _) ∷ _) = ⊤

----------------------------------------------------------------------
-- Construction
--
-- Because the polynomial is stored in a canonical form, we use a
-- normalising cons operator to construct the coefficient lists.
----------------------------------------------------------------------

-- -- Decision procedure for Zero
-- zero? : ∀ {n} → (p : Poly n) → Dec (Zero n p)
-- zero? {zero} (lift x) = zero-c? x
-- zero? {suc n} [] = yes (lift tt)
-- zero? {suc n} (x ∷ xs) = no lower

-- -- Exponentiate the first variable of a polynomial
-- infixr 8 _⍓_
-- _⍓_ : ∀ {n} → Coeffs n → ℕ → Coeffs n
-- [] ⍓ i = []
-- ((x , j) ∷ xs) ⍓ i = (x , j ℕ.+ i) ∷ xs

-- -- Normalising cons
-- infixr 5 _∷↓_
-- _∷↓_ : ∀ {n} → (Poly n × ℕ) → Coeffs n → Coeffs n
-- (x , i) ∷↓ xs with zero? x
-- ... | yes p = xs ⍓ suc i
-- ... | no ¬p = (x ,~ ¬p , i) ∷ xs

-- map-poly : ∀ {n} → (Poly n → Poly n) → Coeffs n → Coeffs n
-- map-poly {n} f = List.foldr cons []
--   where
--   cons : (Coeff n × ℕ) → Coeffs n → Coeffs n
--   cons (x ,~ _ , i) = _∷↓_ (f x , i)

-- ----------------------------------------------------------------------
-- -- Arithmetic
-- ----------------------------------------------------------------------

-- ----------------------------------------------------------------------
-- -- Addition
-- ----------------------------------------------------------------------
-- mutual
--   -- The reason the following code is so verbose is termination
--   -- checking. For instance, in the third case for ⊞-coeffs, we call a
--   -- helper function. Instead, you could conceivably use a with-block
--   -- (on ℕ.compare p q):
--   --
--   -- ⊞-coeffs ((x , p) ∷ xs) ((y , q) ∷ ys) with (ℕ.compare p q)
--   -- ... | ℕ.less    p k = (x , p) ∷ ⊞-coeffs xs ((y , k) ∷ ys)
--   -- ... | ℕ.equal   p   = (fst~ x ⊞ fst~ y , p) ∷↓ ⊞-coeffs xs ys
--   -- ... | ℕ.greater q k = (y , q) ∷ ⊞-coeffs ((x , k) ∷ xs) ys
--   --
--   -- However, because the first and third recursive calls each rewrap
--   -- a list that was already pattern-matched on, the recursive call
--   -- does not strictly decrease the size of its argument.
--   --
--   -- Interestingly, if --without-K is turned off, we don't need the
--   -- helper function ⊞-coeffs; we could pattern match on _⊞_ directly.
--   --
--   -- _⊞_ {zero} (lift x) (lift y) = lift (x + y)
--   -- _⊞_ {suc n} [] ys = ys
--   -- _⊞_ {suc n} (x ∷ xs) [] = x ∷ xs
--   -- _⊞_ {suc n} ((x , p) ∷ xs) ((y , q) ∷ ys) =
--   --   ⊞-ne (ℕ.compare p q) x xs y ys

--   infixl 6 _⊞_
--   _⊞_ : ∀ {n} → Poly n → Poly n → Poly n
--   _⊞_ {zero} (lift x) (lift y) = lift (x + y)
--   _⊞_ {suc n} = ⊞-coeffs

--   ⊞-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
--   ⊞-coeffs [] ys = ys
--   ⊞-coeffs ((x , i) ∷ xs) = ⊞-ne-r i x xs

--   ⊞-ne : ∀ {p q n}
--        → ℕ.Ordering p q
--        → Coeff n
--        → Coeffs n
--        → Coeff n
--        → Coeffs n
--        → Coeffs n
--   ⊞-ne (ℕ.less    i k) x xs y ys = (x , i) ∷ ⊞-ne-r k y ys xs
--   ⊞-ne (ℕ.greater j k) x xs y ys = (y , j) ∷ ⊞-ne-r k x xs ys
--   ⊞-ne (ℕ.equal   i  ) (x ,~ _) xs (y ,~ _) ys =
--     (x ⊞ y , i) ∷↓ ⊞-coeffs xs ys

--   ⊞-ne-r : ∀ {n} → ℕ → Coeff n → Coeffs n → Coeffs n → Coeffs n
--   ⊞-ne-r i x xs [] = (x , i) ∷ xs
--   ⊞-ne-r i x xs ((y , j) ∷ ys) = ⊞-ne (ℕ.compare i j) x xs y ys

-- ----------------------------------------------------------------------
-- -- Negation
-- ----------------------------------------------------------------------

-- ⊟_ : ∀ {n} → Poly n → Poly n
-- ⊟_ {zero} (lift x) = lift (- x)
-- ⊟_ {suc n} = map-poly ⊟_

-- ----------------------------------------------------------------------
-- -- Multiplication
-- ----------------------------------------------------------------------
-- mutual
--   -- Multiply a polynomial in degree n by a Polynomial in degree n-1.
--   infixl 7 _⋊_
--   _⋊_ : ∀ {n} → Poly n → Poly (suc n) → Poly (suc n)
--   _⋊_ = map-poly ∘ _⊠_

--   infixl 7 _⊠_
--   _⊠_ : ∀ {n} → Poly n → Poly n → Poly n
--   _⊠_ {zero} (lift x) (lift y) = lift (x * y)
--   _⊠_ {suc n} = ⊠-coeffs

--   -- A simple shift-and-add algorithm.
--   ⊠-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
--   ⊠-coeffs _ [] = []
--   ⊠-coeffs xs ((y ,~ _ , j) ∷ ys) = List.foldr (⊠-step y ys) [] xs ⍓ j

--   ⊠-step : ∀ {n} → Poly n → Coeffs n → Coeff n × ℕ → Coeffs n → Coeffs n
--   ⊠-step y ys (x ,~ _ , i) xs = (x ⊠ y , i) ∷↓ (x ⋊ ys ⊞ xs)

-- ----------------------------------------------------------------------
-- -- Constants and Variables
-- ----------------------------------------------------------------------

-- -- The constant polynomial
-- κ : ∀ {n} → Carrier → Poly n
-- κ {zero} x = lift x
-- κ {suc n} x = (κ x , 0) ∷↓ []

-- -- A variable
-- ι : ∀ {n} → Fin n → Poly n
-- ι Fin.zero = (κ 1# , 1) ∷↓ []
-- ι (Fin.suc x) = (ι x , 0) ∷↓ []
