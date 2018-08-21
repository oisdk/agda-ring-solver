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

open import Data.Product hiding (Σ)
open import Data.Product.Irrelevant
open import Function
open import Data.Fin as Fin using (Fin)
import Relation.Binary.PropositionalEquality as ≡

-- Multivariate polynomials.
module Polynomials.Ring.Normal
  {a ℓ}
  (coeff : RawRing a)
  (Zero-C : Pred (RawRing.Carrier coeff) ℓ)
  (zero-c? : Decidable Zero-C)
  where

-- This is the one to go for.
--
-- Of the three options, we have:
--
-- 1.
-- data _≤_ : Rel ℕ 0ℓ where
--   z≤n : ∀ {n}                 → zero  ≤ n
--   s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n
--
-- This follows the structure oof its first argument. In other words:
--
--   n ≤ m ≅ fold s≤s z≤n n
--
-- This isn't good, as that first argument is the length of the *rest*
-- of the list:
--
--   [(⋯ , 5 ≤ 6) , (4 ≤ 5), (3 ≤ 4), (1 ≤ 3), (0 ≤ 1)]
--
-- Meaning that consuming it the normal way will be quadratic.
--
-- 2.
-- record _≤″_ (m n : ℕ) : Set where
--   constructor less-than-or-equal
--   field
--     {k}   : ℕ
--     proof : m + k ≡ n
--
-- Also not advantageuos. While it does store the k (which is the
-- size of the gap, which is what we need to use to get linear
-- performance), it doesn't provide any inductive structure, so
-- computations on the k don't provide evidence about the m or n.
-- That said, it works by storing an equality proof, so we could just
-- aggresively erase it, but it's messy (and perhaps unsound).
--
-- 3.
-- data _≤′_ (m : ℕ) : ℕ → Set where
--   ≤′-refl :                         m ≤′ m
--   ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n
--
-- This structure works best. It effectively inducts on the k in 2.,
-- but does so while providing evidence about the overall length.

module Order where
  open import Data.Nat using () renaming (_≤′_ to _≤_) public
  import Data.Nat.Properties as ℕ-≡
  import Relation.Binary.PropositionalEquality.TrustMe as TrustMe

  ≤-trans-pred : ∀ {x y z} → x ≤ y → suc y ≤ z → x ≤ z
  ≤-trans-pred xs ℕ.≤′-refl = ℕ.≤′-step xs
  ≤-trans-pred xs (ℕ.≤′-step ys) = ℕ.≤′-step (≤-trans-pred xs ys)

  data Ordering : ℕ → ℕ → Set where
    less    : ∀ {i j-1} → (i≤j-1 : i ≤ j-1) → Ordering i (suc j-1)
    equal   : ∀ {i}     → Ordering i i
    greater : ∀ {i-1 j} → (j≤i-1 : j ≤ i-1) → Ordering (suc i-1) j

  ≤-compare : ∀ {i j n}
            → (i ≤ n)
            → (j ≤ n)
            → Ordering i j
  ≤-compare ℕ.≤′-refl ℕ.≤′-refl = equal
  ≤-compare ℕ.≤′-refl (ℕ.≤′-step j≤n) = greater j≤n
  ≤-compare (ℕ.≤′-step i≤n) ℕ.≤′-refl = less i≤n
  ≤-compare (ℕ.≤′-step i≤n) (ℕ.≤′-step j≤n) = ≤-compare i≤n j≤n

  z≤n : ∀ {n} → zero ≤ n
  z≤n {zero} = ℕ.≤′-refl
  z≤n {suc n} = ℕ.≤′-step z≤n

  Fin⇒≤ : ∀ {n} (x : Fin n) → suc (Fin.toℕ x) ≤ n
  Fin⇒≤ x = ≡.subst
              (suc (Fin.toℕ x) ≤_)
              (TrustMe.erase (≡.trans (ℕ-≡.+-comm (k x) _) (proof x)))
              (≤⇒≤+ _ ℕ.≤′-refl)
    where
    k : ∀ {n} → Fin n → ℕ
    k {suc n} Fin.zero = n
    k {suc _} (Fin.suc x) = k x

    ≤⇒≤+ : ∀ x {y z} → y ≤ z → y ≤ x ℕ.+ z
    ≤⇒≤+ zero y≤z = y≤z
    ≤⇒≤+ (suc x) y≤z = ℕ.≤′-step (≤⇒≤+ x y≤z)

    proof : ∀ {n} → (x : Fin n) → (suc (Fin.toℕ x) ℕ.+ k x) ≡.≡ n
    proof Fin.zero = ≡.refl
    proof (Fin.suc x) = ≡.cong suc (proof x)

open Order

open RawRing coeff

----------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------

mutual
  -- A Polynomial is indexed by the number of variables it contains.
  infixr 4 _Π_
  record Poly (n : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor _Π_
    field
      {i} : ℕ
      i≤n   : i ≤ n
      flat  : FlatPoly i

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
  Coeffs : ℕ → Set (a ⊔ ℓ)
  Coeffs n = List (ℕ × Coeff n)

  -- We disallow zeroes in the coefficient list. This condition alone
  -- is enough to ensure a unique representation for any polynomial.
  Coeff : ℕ → Set (a ⊔ ℓ)
  Coeff i = Σ~[ x ∈ Poly i ] ¬ Zero x

  Zero : ∀ {n} → Poly n → Set ℓ
  Zero (_ Π Κ x      ) = Zero-C x
  Zero (_ Π Σ []     ) = Lift ℓ ⊤
  Zero (_ Π Σ (_ ∷ _)) = Lift ℓ ⊥

  Norm : ∀ {i} → Coeffs i → Set
  Norm [] = ⊥
  Norm ((zero  , _) ∷ []) = ⊥
  Norm ((zero  , _) ∷ _ ∷ _) = ⊤
  Norm ((suc _ , _) ∷ _) = ⊤

open Poly

----------------------------------------------------------------------
-- Construction
--
-- Because the polynomial is stored in a canonical form, we use a
-- normalising cons operator to construct the coefficient lists.
----------------------------------------------------------------------

-- Decision procedure for Zero
zero? : ∀ {n} → (p : Poly n) → Dec (Zero p)
zero? (_ Π Κ x      ) = zero-c? x
zero? (_ Π Σ []     ) = yes (lift tt)
zero? (_ Π Σ (_ ∷ _)) = no lower

-- Exponentiate the first variable of a polynomial
infixr 8 _⍓_
_⍓_ : ∀ {n} → Coeffs n → ℕ → Coeffs n
[] ⍓ i = []
((j , x) ∷ xs) ⍓ i = (j ℕ.+ i , x) ∷ xs

-- Normalising cons
infixr 5 _^_∷↓_
_^_∷↓_ : ∀ {n} → Poly n → ℕ → Coeffs n → Coeffs n
x ^ i ∷↓ xs with zero? x
... | yes p = xs ⍓ suc i
... | no ¬p = (i , x ,~ ¬p) ∷ xs

-- Inject a polynomial into a larger polynomoial with more variables
_Π↑_ : ∀ {n m} → (suc n ≤ m) → Poly n → Poly m
n≤m Π↑ (i≤n Π xs) = (≤-trans-pred i≤n n≤m) Π xs

infixr 4 _Π↓_
_Π↓_ : ∀ {i n} → suc i ≤ n → Coeffs i → Poly n
i≤n Π↓ []                      = z≤n Π Κ 0#
i≤n Π↓ ((zero , x ,~ _ ) ∷ []) = i≤n Π↑ x
i≤n Π↓ ((zero , x₁) ∷ x₂ ∷ xs) = i≤n Π Σ ((zero , x₁) ∷ x₂ ∷ xs)
i≤n Π↓ ((suc j , x) ∷ xs)      = i≤n Π Σ ((suc j , x) ∷ xs)

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
  (i≤n Π xs) ⊞ (j≤n Π ys) = ⊞-inj (≤-compare i≤n j≤n) xs i≤n ys j≤n

  ⊞-inj : ∀ {i j n}
        → Ordering i j
        → FlatPoly i
        → (i ≤ n)
        → FlatPoly j
        → (j ≤ n)
        → Poly n
  ⊞-inj equal (Κ x)  i≤n (Κ y)  j≤n   = i≤n Π Κ (x + y)
  ⊞-inj equal (Σ xs) i≤n (Σ ys) j≤n   = i≤n Π↓ ⊞-coeffs xs ys
  ⊞-inj (less    i≤j-1) xs i≤n ys j≤n = j≤n Π↓ ⊞-le i≤j-1 xs ys
  ⊞-inj (greater j≤i-1) xs i≤n ys j≤n = i≤n Π↓ ⊞-le j≤i-1 ys xs

  ⊞-le : ∀ {i k}
       → (i ≤ k)
       → FlatPoly i
       → FlatPoly (suc k)
       → Coeffs k
  ⊞-le i≤k xs (Σ [] {()})
  ⊞-le i≤k xs (Σ ((zero , (j≤k Π y) ,~ _ ) ∷ ys)) =
    ⊞-inj (≤-compare j≤k i≤k) y j≤k xs i≤k ^ zero ∷↓ ys
  ⊞-le i≤k xs (Σ ((suc j , y) ∷ ys)) =
    (i≤k Π xs) ^ zero ∷↓ (j , y) ∷ ys

  ⊞-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
  ⊞-coeffs [] ys = ys
  ⊞-coeffs ((i , x) ∷ xs) = ⊞-ne-r i x xs

  ⊞-ne : ∀ {p q n}
       → ℕ.Ordering p q
       → Coeff n
       → Coeffs n
       → Coeff n
       → Coeffs n
       → Coeffs n
  ⊞-ne (ℕ.less    i k) x xs y ys = (i , x) ∷ ⊞-ne-r k y ys xs
  ⊞-ne (ℕ.greater j k) x xs y ys = (j , y) ∷ ⊞-ne-r k x xs ys
  ⊞-ne (ℕ.equal   i  ) (x ,~ _) xs (y ,~ _) ys =
    (x ⊞ y) ^ i ∷↓ ⊞-coeffs xs ys

  ⊞-ne-r : ∀ {n} → ℕ → Coeff n → Coeffs n → Coeffs n → Coeffs n
  ⊞-ne-r i x xs [] = (i , x) ∷ xs
  ⊞-ne-r i x xs ((j , y) ∷ ys) = ⊞-ne (ℕ.compare i j) x xs y ys

----------------------------------------------------------------------
-- Negation
----------------------------------------------------------------------

⊟_ : ∀ {n} → Poly n → Poly n
⊟_ (i≤n Π Κ x) = i≤n Π Κ (- x)
⊟_ (i≤n Π Σ xs) = i≤n Π↓ go xs
  where
  go : ∀ {n} → Coeffs n → Coeffs n
  go ((i , x ,~ _) ∷ xs) = ⊟ x ^ i ∷↓ go xs
  go [] = []

----------------------------------------------------------------------
-- Multiplication
----------------------------------------------------------------------
mutual
  infixl 7 _⊠_
  _⊠_ : ∀ {n} → Poly n → Poly n → Poly n
  (i≤n Π xs) ⊠ (j≤n Π ys) = ⊠-inj (≤-compare i≤n j≤n) xs i≤n ys j≤n

  ⊠-le : ∀ {i k}
       → i ≤ k
       → FlatPoly i
       → Coeffs k
       → Coeffs k
  ⊠-le i≤k x [] = []
  ⊠-le i≤k x ((p , ((j≤k Π y) ,~ _)) ∷ ys) =
    ⊠-inj (≤-compare i≤k j≤k) x i≤k y j≤k ^ p ∷↓ ⊠-le i≤k x ys

  ⊠-inj : ∀ {i j n}
        → Ordering i j
        → FlatPoly i
        → (i ≤ n)
        → FlatPoly j
        → (j ≤ n)
        → Poly n
  ⊠-inj equal (Κ x)  i≤n (Κ y)  j≤n = i≤n Π Κ (x + y)
  ⊠-inj equal (Σ xs) i≤n (Σ ys) j≤n = i≤n Π↓ ⊠-coeffs xs ys
  ⊠-inj (less    i≤j-1) xs i≤n (Σ ys) j≤n = j≤n Π↓ ⊠-le i≤j-1 xs ys
  ⊠-inj (greater j≤i-1) (Σ xs) i≤n ys j≤n = i≤n Π↓ ⊠-le j≤i-1 ys xs

  -- A simple shift-and-add algorithm.
  ⊠-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
  ⊠-coeffs _ [] = []
  ⊠-coeffs xs ((j , y ,~ _ ) ∷ ys) = ⊠-step y ys xs ⍓ j

  ⊠-step : ∀ {n} → Poly n → Coeffs n → Coeffs n → Coeffs n
  ⊠-step y ys [] = []
  ⊠-step y ys ((i , (j≤n Π x) ,~ _ ) ∷ xs) =
    ((j≤n Π x) ⊠ y) ^ i ∷↓ ⊞-coeffs (⊠-le j≤n x ys) (⊠-step y ys xs)

----------------------------------------------------------------------
-- Constants and Variables
----------------------------------------------------------------------

-- The constant polynomial
κ : ∀ {n} → Carrier → Poly n
κ x = z≤n Π Κ x

-- A variable
ι : ∀ {n} → Fin n → Poly n
ι i = Fin⇒≤ i Π↓ (κ 1# ^ 1 ∷↓ [])
