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
  renaming (_≤″_ to _≤_)
open import Data.Product
open import Data.Product.Irrelevant
open import Function
open import Data.Fin as Fin using (Fin)
import Relation.Binary.PropositionalEquality as ≡
import Data.Nat.Properties as ℕ-≡

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
      flat : NormPoly i
      .i≤n  : i ≤ n

  FlatPoly : ℕ → Set (a ⊔ ℓ)
  FlatPoly zero = Lift ℓ Carrier
  FlatPoly (suc n) = Coeffs n

  NormPoly : ℕ → Set (a ⊔ ℓ)
  NormPoly i = Σ~ (FlatPoly i) (Norm i)

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

open NestPoly

----------------------------------------------------------------------
-- Construction
--
-- Because the polynomial is stored in a canonical form, we use a
-- normalising cons operator to construct the coefficient lists.
----------------------------------------------------------------------

-- Decision procedure for Zero
zero? : ∀ {n} → (p : Poly n) → Dec (Zero p)
zero? (zero  , lift x  ,~ _ [,] _) = zero-c? x
zero? (suc _ , []      ,~ _ [,] _) = yes (lift tt)
zero? (suc _ , (_ ∷ _) ,~ _ [,] _) = no lower

-- Exponentiate the first variable of a polynomial
infixr 8 _⍓_
_⍓_ : ∀ {n} → Coeffs n → ℕ → Coeffs n
[] ⍓ i = []
((x , j) ∷ xs) ⍓ i = (x , j ℕ.+ i) ∷ xs

-- Normalising cons
infixr 5 _^_∷↓_
_^_∷↓_ : ∀ {n} → Poly n → ℕ → Coeffs n → Coeffs n
x ^ i ∷↓ xs with zero? x
... | yes p = xs ⍓ suc i
... | no ¬p = (x ,~ ¬p , i) ∷ xs

map-poly : ∀ {n} → (Poly n → Poly n) → Coeffs n → Coeffs n
map-poly {n} f = List.foldr cons []
  where
  cons : (Coeff n × ℕ) → Coeffs n → Coeffs n
  cons (x ,~ _ , i) = f x ^ i ∷↓_

≤-trans : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
≤-trans (ℕ.less-than-or-equal {k₁} xs) (ℕ.less-than-or-equal {k₂} ys) =
  ℕ.less-than-or-equal {k = k₁ ℕ.+ k₂}
  (≡.trans (≡.sym (ℕ-≡.+-assoc _ k₁ k₂))
  (≡.trans (≡.cong (ℕ._+ k₂) xs) ys))

z≤n : ∀ {n} → zero ≤ n
z≤n = ℕ.less-than-or-equal ≡.refl

≤-left-pred : ∀ {x y} → suc x ≤ y → x ≤ y
≤-left-pred (ℕ.less-than-or-equal proof) =
  ℕ.less-than-or-equal (≡.trans (ℕ-≡.+-suc _ _) proof)

x≤x+k : ∀ {x k} → x ≤ x ℕ.+ k
x≤x+k = ℕ.less-than-or-equal ≡.refl

-- Inject a polynomial into a larger polynomoial with more variables
inject : ∀ {n m} → Poly n → .(n ≤ m) → Poly m
inject (_ , xs [,] i≤n) n≤m = _ , xs [,] (≤-trans i≤n n≤m)

infixr 4 _[,]↓_
_[,]↓_ : ∀ {i n} → FlatPoly i → .(i ≤ n) → Poly n
_[,]↓_ {zero}  xs i≤n = zero , xs ,~ tt [,] i≤n
_[,]↓_ {suc i} [] i≤n = zero , lift 0# ,~ tt [,] z≤n
_[,]↓_ {suc i} ((x ,~ _ , zero) ∷ []) i≤n = inject x (≤-left-pred i≤n)
_[,]↓_ {suc i} ((x₁ , zero) ∷ x₂ ∷ xs) i≤n =
  suc i , ((x₁ , zero) ∷ x₂ ∷ xs) ,~ tt [,] i≤n
_[,]↓_ {suc i} ((x , suc j) ∷ xs) i≤n =
  suc i , ((x , suc j) ∷ xs) ,~ tt [,] i≤n

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
  --   ⊞-ne (ℕ.compare p q) x xs y ys

  infixl 6 _⊞_
  _⊞_ : ∀ {n} → Poly n → Poly n → Poly n
  (i , xs [,] xs≤) ⊞ (j , ys [,] ys≤) = ⊞-inj (ℕ.compare i j) xs xs≤ ys ys≤

  ⊞-inj : ∀ {i j n}
        → ℕ.Ordering i j
        → NormPoly i
        → .(i ≤ n)
        → NormPoly j
        → .(j ≤ n)
        → Poly n
  ⊞-inj (ℕ.equal   m  ) xs i≤n ys _ = ⊞-flat _ xs ys i≤n
  ⊞-inj (ℕ.less    m k) xs x≤ ys y≤ = ⊞-le xs x≤ ys y≤
  ⊞-inj (ℕ.greater m k) xs x≤ ys y≤ = ⊞-le ys y≤ xs x≤

  ⊞-flat : ∀ i {n} → NormPoly i → NormPoly i → .(i ≤ n) → Poly n
  ⊞-flat zero (lift x ,~ _) (lift y ,~ _) i≤n = zero , lift (x + y) ,~ tt [,] i≤n
  ⊞-flat (suc i) (xs ,~ _) (ys ,~ _) i≤n = ⊞-coeffs xs ys [,]↓ i≤n

  ⊞-le : ∀ {i k n}
       → NormPoly i
       → .(i ≤ n)
       → NormPoly (suc (i ℕ.+ k))
       → .(suc (i ℕ.+ k) ≤ n)
       → Poly n
  ⊞-le xs _ ([] ,~ ()) i≤n
  ⊞-le xs xs≤ ((((j , y [,] y≤) ,~ _ , zero) ∷ ys) ,~ yn) k≤n =
    (⊞-inj (ℕ.compare _ _) y y≤ xs x≤x+k ^ zero ∷↓ ys) [,]↓ k≤n
  ⊞-le xs i≤n (((y , suc j) ∷ ys) ,~ yn) j≤n =
    ((_ , xs [,] x≤x+k) ^ zero ∷↓ (y , j) ∷ ys) [,]↓ j≤n

  ⊞-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
  ⊞-coeffs [] ys = ys
  ⊞-coeffs ((x , i) ∷ xs) = ⊞-ne-r i x xs

  ⊞-ne : ∀ {p q n}
       → ℕ.Ordering p q
       → Coeff n
       → Coeffs n
       → Coeff n
       → Coeffs n
       → Coeffs n
  ⊞-ne (ℕ.less    i k) x xs y ys = (x , i) ∷ ⊞-ne-r k y ys xs
  ⊞-ne (ℕ.greater j k) x xs y ys = (y , j) ∷ ⊞-ne-r k x xs ys
  ⊞-ne (ℕ.equal   i  ) (x ,~ _) xs (y ,~ _) ys =
    (x ⊞ y) ^ i ∷↓ ⊞-coeffs xs ys

  ⊞-ne-r : ∀ {n} → ℕ → Coeff n → Coeffs n → Coeffs n → Coeffs n
  ⊞-ne-r i x xs [] = (x , i) ∷ xs
  ⊞-ne-r i x xs ((y , j) ∷ ys) = ⊞-ne (ℕ.compare i j) x xs y ys

-- ----------------------------------------------------------------------
-- -- Negation
-- ----------------------------------------------------------------------

-- ⊟_ : ∀ {n} → Poly n → Poly n
-- ⊟_ (zero  , lift x ,~ xn [,] i≤n) = zero , lift (- x) ,~ xn [,] i≤n
-- ⊟_ (suc n , xs     ,~ xn [,] i≤n) = map-poly ⊟_ xs [,]↓ i≤n

----------------------------------------------------------------------
-- Multiplication
----------------------------------------------------------------------
mutual
  _⋊_ : ∀ {n} → Poly n → Coeffs n → Coeffs n
  xs ⋊ [] = []
  xs ⋊ ((y ,~ y≠0 , j) ∷ ys) = (xs ⊠ y) ^ j ∷↓ (xs ⋊ ys)

  infixl 7 _⊠_
  _⊠_ : ∀ {n} → Poly n → Poly n → Poly n
  (i , xs [,] i≤n) ⊠ (j , ys [,] j≤n) = ⊠-inj (ℕ.compare i j) xs i≤n ys j≤n

  ⊠-up : ∀ {i k n}
       → NormPoly i
       → .(i ≤ n)
       → NormPoly (suc (i ℕ.+ k))
       → .(suc (i ℕ.+ k) ≤ n)
       → Poly n
  ⊠-up xs xs≤ (ys ,~ _) ys≤ =
    ⊠-up′ xs xs≤ ys [,]↓ ys≤

  ⊠-up′ : ∀ {i k n}
       → NormPoly i
       → .(i ≤ n)
       → Coeffs (i ℕ.+ k)
       → Coeffs (i ℕ.+ k)
  ⊠-up′ xs xs≤ [] = []
  ⊠-up′ xs xs≤ ((((p , y [,] y≤) ,~ _ , j) ∷ ys)) =
    (⊠-inj (ℕ.compare _ _) y y≤ xs x≤x+k) ^ j ∷↓ ⊠-up′ xs xs≤ ys


  ⊠-inj : ∀ {i j n}
        → ℕ.Ordering i j
        → NormPoly i
        → .(i ≤ n)
        → NormPoly j
        → .(j ≤ n)
        → Poly n
  ⊠-inj (ℕ.equal     k) xs i≤n ys j≤n = ⊠-flat _ xs ys i≤n
  ⊠-inj (ℕ.greater j k) xs i≤n ys j≤n = ⊠-up ys j≤n xs i≤n
  ⊠-inj (ℕ.less    i k) xs i≤n ys j≤n = ⊠-up xs i≤n ys j≤n

  ⊠-flat : ∀ i {n}
         → NormPoly i
         → NormPoly i
         → .(i ≤ n)
         → Poly n
  ⊠-flat zero (lift x ,~ _) (lift y ,~ _) i≤n = zero , lift (x * y) ,~ tt [,] i≤n
  ⊠-flat (suc i) (xs ,~ _) (ys ,~ _) i≤n = ⊠-coeffs xs ys [,]↓ i≤n


  -- A simple shift-and-add algorithm.
  ⊠-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
  ⊠-coeffs _ [] = []
  ⊠-coeffs xs ((y ,~ _ , j) ∷ ys) = ⊠-step y ys xs ⍓ j

  ⊠-step : ∀ {n} → Poly n → Coeffs n → Coeffs n → Coeffs n
  ⊠-step y ys [] = []
  ⊠-step y ys ((x ,~ _ , i) ∷ xs) = (x ⊠ y) ^ i ∷↓ ⊞-coeffs (x ⋊ ys) (⊠-step y ys xs)

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
