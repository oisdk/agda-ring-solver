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
  using (ℕ; suc; zero; _≤_)
open import Data.Nat.Properties as ℕ-≡

open import Data.Product hiding (Σ)
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

module Orders where
  open ≡
  open ≡.≡-Reasoning
  open import Data.Nat
  open import Data.Nat.Properties
  import Relation.Binary.PropositionalEquality.TrustMe as TrustMe

  ⇒≤-trans : ∀ {x y z n m} → n + x ≡ y → m + y ≡ z → (m + n) + x ≡ z
  ⇒≤-trans {x} {y} {z} {n} {m} xs ys = TrustMe.erase $
    begin
      m + n + x
    ≡⟨ +-assoc m n x ⟩
      m + (n + x)
    ≡⟨ cong (m +_) xs ⟩
      m + y
    ≡⟨ ys ⟩
      z
    ∎

  x⇒0≤x : ∀ {x} → x + 0 ≡ x
  x⇒0≤x = TrustMe.erase (+-identityʳ _)

  ⇒≤-pred-l : ∀ {inj x y} → inj + suc x ≡ y → suc inj + x ≡ y
  ⇒≤-pred-l xs = TrustMe.erase (trans (sym (+-suc _ _)) xs)

  ⇒≤-pos : ∀ x y {i n} → i + x ≡ n → i + y ≡ n → x ≡ y
  ⇒≤-pos _ _ xs ys = TrustMe.erase (+-cancelˡ-≡ _ (trans xs (sym ys)))

  join-cmp : ∀ i k x y {n} → suc (i + k + y) ≡ n → i + x ≡ n → x ≡ suc (y + k)
  join-cmp i k x y xpr ypr = TrustMe.erase lem
    where
    lem : x ≡ suc (y + k)
    lem = sym (trans (cong suc (+-comm y k)) (+-cancelˡ-≡ i (trans (+-suc i (k + y)) (trans (cong suc (sym (+-assoc i k y))) (trans xpr (sym ypr))))))

  cmpSwap : ∀ x y {n i j} → Ordering i j → i + x ≡ n → j + y ≡ n → Ordering x y
  cmpSwap x y (less    i k) i+x≡n j+y≡n rewrite join-cmp i k x y j+y≡n i+x≡n = greater y k
  cmpSwap x y (equal     m) i+x≡n j+y≡n rewrite ⇒≤-pos x y i+x≡n j+y≡n       = equal y
  cmpSwap x y (greater j k) i+x≡n j+y≡n rewrite join-cmp j k y x i+x≡n j+y≡n = less x k

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
      {inj} : ℕ
      .i≤n  : inj ≤ n
      flat  : FlatPoly inj

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
_Π↑_ : ∀ {n m} → .(n ≤ m) → Poly n → Poly m
n≤m Π↑ (i≤n Π xs) = (ℕ-≡.≤-trans i≤n n≤m) Π xs

infixr 4 _Π↓_
_Π↓_ : ∀ {i n} → .(suc i ≤ n) → Coeffs i → Poly n
i≤n Π↓ []                       = ℕ.z≤n Π Κ 0#
i≤n Π↓ ((zero , x ,~ _ )  ∷ []) = ℕ-≡.≤⇒pred≤ i≤n Π↑ x
i≤n Π↓ ((zero , x₁ ) ∷ x₂ ∷ xs) = i≤n Π Σ ((zero , x₁) ∷ x₂ ∷ xs)
i≤n Π↓ ((suc j , x) ∷ xs)       = i≤n Π Σ ((suc j , x) ∷ xs)

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
  (i≤n Π xs) ⊞ (j≤n Π ys) = ⊞-inj (ℕ.compare _ _) xs i≤n ys j≤n

  ⊞-inj : ∀ {i j n}
        → ℕ.Ordering i j
        → FlatPoly i
        → .(i ≤ n)
        → FlatPoly j
        → .(j ≤ n)
        → Poly n
  ⊞-inj (ℕ.equal   _  ) (Κ x) i≤n (Κ y) _ = i≤n Π Κ (x + y)
  ⊞-inj (ℕ.equal   _  ) (Σ xs) i≤n (Σ ys) _ = i≤n Π↓ ⊞-coeffs xs ys
  ⊞-inj (ℕ.less    _ _) xs i≤n ys j≤n = ⊞-le xs i≤n ys j≤n
  ⊞-inj (ℕ.greater _ _) xs i≤n ys j≤n = ⊞-le ys j≤n xs i≤n

  ⊞-le : ∀ {i k n}
       → FlatPoly i
       → .(i ≤ n)
       → FlatPoly (suc (i ℕ.+ k))
       → .(suc (i ℕ.+ k) ≤ n)
       → Poly n
  ⊞-le xs _ (Σ [] {()})
  ⊞-le xs xs≤ (Σ ((zero , (y≤ Π y) ,~ _ ) ∷ ys)) = _Π↓
    (⊞-inj (ℕ.compare _ _) y y≤ xs (ℕ-≡.m≤m+n _ _) ^ zero ∷↓ ys)
  ⊞-le xs i≤n (Σ ((suc j , y) ∷ ys)) = _Π↓
    (((ℕ-≡.m≤m+n _ _) Π xs) ^ zero ∷↓ (j , y) ∷ ys)

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
  _⋊_ : ∀ {n} → Poly n → Coeffs n → Coeffs n
  xs ⋊ [] = []
  xs ⋊ ((j , y ,~ y≠0) ∷ ys) = (xs ⊠ y) ^ j ∷↓ (xs ⋊ ys)

  infixl 7 _⊠_
  _⊠_ : ∀ {n} → Poly n → Poly n → Poly n
  (i≤n Π xs) ⊠ (j≤n Π ys) = ⊠-inj (ℕ.compare _ _) xs i≤n ys j≤n

  ⊠-up : ∀ {i k n}
       → FlatPoly i
       → .(i ≤ n)
       → Coeffs (i ℕ.+ k)
       → Coeffs (i ℕ.+ k)
  ⊠-up _ _ [] = []
  ⊠-up xs i≤n (((j , (y≤  Π y) ,~ _ ) ∷ ys)) =
    (⊠-inj (ℕ.compare _ _) y y≤ xs (ℕ-≡.m≤m+n _ _)) ^ j ∷↓ ⊠-up xs i≤n ys

  ⊠-inj : ∀ {i j n}
        → ℕ.Ordering i j
        → FlatPoly i
        → .(i ≤ n)
        → FlatPoly j
        → .(j ≤ n)
        → Poly n
  ⊠-inj (ℕ.equal _) xs i≤n ys j≤n = ⊠-eq xs ys i≤n
  ⊠-inj (ℕ.greater j k) (Σ xs) i≤n ys j≤n = i≤n Π↓ ⊠-up ys j≤n xs
  ⊠-inj (ℕ.less    i k) xs i≤n (Σ ys) j≤n = j≤n Π↓ ⊠-up xs i≤n ys

  ⊠-eq : ∀ {i n}
       → FlatPoly i
       → FlatPoly i
       → .(i ≤ n)
       → Poly n
  ⊠-eq (Κ x)  (Κ y)  i≤n = i≤n Π Κ (x * y)
  ⊠-eq (Σ xs) (Σ ys) i≤n = i≤n Π↓ ⊠-coeffs xs ys

  -- A simple shift-and-add algorithm.
  ⊠-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
  ⊠-coeffs _ [] = []
  ⊠-coeffs xs ((j , y ,~ _ ) ∷ ys) = ⊠-step y ys xs ⍓ j

  ⊠-step : ∀ {n} → Poly n → Coeffs n → Coeffs n → Coeffs n
  ⊠-step y ys [] = []
  ⊠-step y ys ((i , x ,~ _ ) ∷ xs) = (x ⊠ y) ^ i ∷↓ ⊞-coeffs (x ⋊ ys) (⊠-step y ys xs)

-- ----------------------------------------------------------------------
-- -- Constants and Variables
-- ----------------------------------------------------------------------

-- The constant polynomial
κ : ∀ {n} → Carrier → Poly n
κ x = ℕ.z≤n Π Κ x

Fin⇒≤ : ∀ {n} → (x : Fin n) → suc (Fin.toℕ x) ≤ n
Fin⇒≤ Fin.zero = ℕ.s≤s ℕ.z≤n
Fin⇒≤ (Fin.suc x) = ℕ.s≤s (Fin⇒≤ x)

-- A variable
ι : ∀ {n} → Fin n → Poly n
ι i = Fin⇒≤ i Π↓ (κ 1# ^ 1 ∷↓ [])
