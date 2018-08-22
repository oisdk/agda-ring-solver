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
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Function
open import Data.Fin as Fin using (Fin)

-- Multivariate polynomials.
module Polynomials.Ring.Normal
  {a ℓ}
  (coeffs : RawRing a)
  (Zero-C : Pred (RawRing.Carrier coeffs) ℓ)
  (zero-c? : Decidable Zero-C)
  where

----------------------------------------------------------------------
-- Gaps
----------------------------------------------------------------------
-- Polynomials can be represented as lists of their coefficients,
-- stored in increasing powers of x:
--
--   3 + 2x² + 4x⁵ + 2x⁷
-- ≡⟨ making the missing xs explicit ⟩
--   3x⁰ + 0x¹ + 2x² + 0x³ + 0x⁴ + 4x⁵ + 0x⁶ + 2x⁷
-- ≡⟨ in list notation ⟩
--   [3,0,2,0,0,4,0,2]
--
-- However, as described in:
--   B. Grégoire and A. Mahboubi, ‘Proving Equalities in a Commutative
--   Ring Done Right in Coq’, in Theorem Proving in Higher Order
--   Logics, Berlin, Heidelberg, 2005, vol. 3603, pp. 98–113.
--
-- This approach is wasteful with space. Instead, we will pair each
-- coefficient with the size of the preceding gap, meaning that the
-- above expression is instead written as:
--
--   [(3,0),(2,1),(4,2),(2,1)]
--
-- Which can be thought of as a representation of the expression:
--
--   x⁰ * (3 + x * x¹ * (2 + x * x² * (4 + x * x¹ * (2 + x * 0))))
--
-- To add multiple variables to a polynomial, you can *nest* them,
-- making the coefficients of the outer polynomial polynomials
-- themselves. However, this is *also* wasteful, in a similar way to
-- above: the constant polynomial, for instance, will be represented
-- as many nestings of constant polynomials around a final variable.
-- However, this approach presents a difficulty: the polynomial will
-- have the kind ℕ → Set (...). In other words, it's indexed by the
-- number of variables it contains. The gap we store, then, has to
-- be accomanied with some information about how it relates to that
-- index.
--
-- The first approach I tried was to forget about storing the gaps,
-- and instead store the number of variables in the nested coefficient,
-- along with a proof that the number was smaller than the outer. The
-- proof was _≤_ from Data.Nat:
--
-- data _≤_ : Rel ℕ 0ℓ where
--   z≤n : ∀ {n}                 → zero  ≤ n
--   s≤s : ∀ {m n} (m≤n : m ≤ n) → suc m ≤ suc n
--
-- While this worked, this will actually give you a worse complexity
-- than the naive encoding without gaps.
--
-- For any of the binary operations, you need to be able to "line up"
-- the two arguments in terms of the gaps. For addition, for instance,
-- the argument with fewer variables should be added to the constant
-- term of the argument with more. To do this, you need to compare the
-- gaps.
--
-- To see why that's a problem, consider the following sequence of
-- nestings:
--
--   (5 ≤ 6), (4 ≤ 5), (3 ≤ 4), (1 ≤ 3), (0 ≤ 1)
--
-- The outer polynomial has 6 variables, but it has a gap to its inner
-- polynomial of 5, and so on. What we compare in this case is the
-- number of variables in the tail: like repeatedly taking the tail of
-- a list, it's quadratic.
--
-- The second approach was to try and mimic the powers structure
-- (which only compared the gaps, which is linear), and store the gaps
-- in a proof like the following:
--
-- record _≤″_ (m n : ℕ) : Set where
--   constructor less-than-or-equal
--   field
--     {k}   : ℕ
--     proof : m + k ≡ n
--
-- Here, k is the size of the gap. The problem of this approach was
-- twofold: it was difficult to show that comparisons on the k
-- corresponded to comparisons on the m, and working with ≡ instead of
-- some inductive structure was messy. However, it had the advantage
-- of being erasable: both proofs of the correspondence and the
-- equality proof itself. That said, I'm not very familiar with the
-- soundness of erasure, and in particular how it interacts with axiom
-- K (which I'd managed to avoid up until this point, but started to
-- creep in).
--
-- I may have had more luck if I swapped the arguments too +:
--
-- record _≤″_ (m n : ℕ) : Set where
--   constructor less-than-or-equal
--   field
--     {k}   : ℕ
--     proof : k + m ≡ n
--
-- But I did not try it. The solution I ended up with was superior,
-- regardless:
--
-- data _≤′_ (m : ℕ) : ℕ → Set where
--   ≤′-refl :                         m ≤′ m
--   ≤′-step : ∀ {n} (m≤′n : m ≤′ n) → m ≤′ suc n
--
-- While this structure stores the same information as ≤, it does so
-- by induction on the *gap*. This became apparent when I realised you
-- could use it to write a comparison function which was linear in the
-- size of the gap (even though it was comparing the length of the
-- tail):
--
-- infix 4 _≤_
-- data _≤_ (m : ℕ) : ℕ → Set where
--   m≤m : m ≤ m
--   ≤-s : ∀ {n} → (m≤n : m ≤ n) → m ≤ suc n

-- data Ordering : ℕ → ℕ → Set where
--   less    : ∀ {n m} → n ≤ m → Ordering n (suc m)
--   greater : ∀ {n m} → m ≤ n → Ordering (suc n) m
--   equal   : ∀ {n}           → Ordering n n

-- ≤-compare : ∀ {i j n}
--           → (i≤n : i ≤ n)
--           → (j≤n : j ≤ n)
--           → Ordering i j
-- ≤-compare m≤m m≤m = equal
-- ≤-compare m≤m (≤-s m≤n) = greater m≤n
-- ≤-compare (≤-s m≤n) m≤m = less m≤n
-- ≤-compare (≤-s i≤n) (≤-s j≤n) = ≤-compare i≤n j≤n
--
-- A few things too note here:
--
-- 1. I'm using my own definition of _≤″_, rather than the one in
--    Data.Nat.
-- 2. The ≤-compare function is one of those reassuring ones for which
--    Agda can completely fill in the type for me.
-- 3. This function looks somewhat similar to the one for comparing ℕ
--    in Data.Nat, and as a result, the "matching" logic for degree
--    and number of variables began too look similar.
--
-- While this approach allowed me too write all the functions I
-- needed, I hit another roadblock when it came time to prove the
-- ring homomorphism. The first thing I realised I needed to prove was
-- basically the following:
--
--   ∀ {i j n}
--   → (i≤n : i ≤ n)
--   → (j≤n : j ≤ n)
--   → ∀ xs Ρ
--   → Σ⟦ xs ⟧ (drop-1 i≤n Ρ) ≈ Σ⟦ xs ⟧ (drop-1 j≤n Ρ)
--
-- In effect, if the inequalities are over the same numbers, then
-- they'll behave the same way when used in evaluation.
--
-- The above is really just a consequence of ≤ being irrelevant:
--
--   ∀ {i n}
--   → (x : i ≤ n)
--   → (y : i ≤ n)
--   → x ≡ y
--
infix 4 _≤_
data _≤_ (m : ℕ) : ℕ → Set where
  m≤m : m ≤ m
  ≤-s : ∀ {n} → (m≤n : m ≤ n) → m ≤ suc n

infixl 6 _⋈_
_⋈_ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
xs ⋈ m≤m = xs
xs ⋈ (≤-s ys) = ≤-s (xs ⋈ ys)


data Ordering {n : ℕ} : ∀ {i j}
                      → (i≤n : i ≤ n)
                      → (j≤n : j ≤ n)
                      → Set
                      where
  _<_ : ∀ {i j-1}
      → (i≤j-1 : i ≤ j-1)
      → (j≤n : suc j-1 ≤ n)
      → Ordering (≤-s i≤j-1 ⋈ j≤n) j≤n
  _>_ : ∀ {i-1 j}
      → (i≤n : suc i-1 ≤ n)
      → (j≤i-1 : j ≤ i-1)
      → Ordering i≤n (≤-s j≤i-1 ⋈ i≤n)
  eq : ∀ {i} → (i≤n : i ≤ n) → Ordering i≤n i≤n

_∺_ : ∀ {i j n}
    → (x : i ≤ n)
    → (y : j ≤ n)
    → Ordering x y
m≤m ∺ m≤m = eq m≤m
m≤m ∺ ≤-s y = m≤m > y
≤-s x ∺ m≤m = x < m≤m
≤-s x ∺ ≤-s y with x ∺ y
≤-s .(≤-s i≤j-1 ⋈ y) ∺ ≤-s y            | i≤j-1 < .y = i≤j-1 < ≤-s y
≤-s x            ∺ ≤-s .(≤-s j≤i-1 ⋈ x) | .x > j≤i-1 = ≤-s x > j≤i-1
≤-s x            ∺ ≤-s .x           | eq .x = eq (≤-s x)

z≤n : ∀ {n} → zero ≤ n
z≤n {zero} = m≤m
z≤n {suc n} = ≤-s z≤n

space : ∀ {n} → Fin n → ℕ
space {suc n} Fin.zero = n
space {suc _} (Fin.suc x) = space x

Fin⇒≤ : ∀ {n} (x : Fin n) → suc (space x) ≤ n
Fin⇒≤ Fin.zero = m≤m
Fin⇒≤ (Fin.suc x) = ≤-s (Fin⇒≤ x)

open RawRing coeffs

----------------------------------------------------------------------
-- Definitions
----------------------------------------------------------------------

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
  infixl 6 _Δ_
  record CoeffExp (i : ℕ) : Set (a ⊔ ℓ) where
    inductive
    constructor _Δ_
    field
      coeff : Coeff i
      pow   : ℕ

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

-- Normalising cons
infixr 5 _^_∷↓_
_^_∷↓_ : ∀ {n} → Poly n → ℕ → Coeffs n → Coeffs n
x ^ i ∷↓ xs with zero? x
... | yes p = xs ⍓ suc i
... | no ¬p = _≠0 x {¬p} Δ i ∷ xs

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
  (xs Π i≤n) ⊞ (ys Π j≤n) = ⊞-match (i≤n ∺ j≤n) xs ys

  ⊞-match : ∀ {i j n}
        → {i≤n : i ≤ n}
        → {j≤n : j ≤ n}
        → Ordering i≤n j≤n
        → FlatPoly i
        → FlatPoly j
        → Poly n
  ⊞-match (eq i&j≤n)    (Κ x)  (Κ y)  = Κ (x + y)         Π  i&j≤n
  ⊞-match (eq i&j≤n)    (Σ xs) (Σ ys) = ⊞-coeffs    xs ys Π↓ i&j≤n
  ⊞-match (i≤j-1 < j≤n)  xs    (Σ ys) = ⊞-inj i≤j-1 xs ys Π↓ j≤n
  ⊞-match (i≤n > j≤i-1) (Σ xs)  ys    = ⊞-inj j≤i-1 ys xs Π↓ i≤n

  ⊞-inj : ∀ {i k}
       → (i ≤ k)
       → FlatPoly i
       → Coeffs k
       → Coeffs k
  ⊞-inj i≤k xs [] = xs Π i≤k ^ zero ∷↓ []
  ⊞-inj i≤k xs (y Π j≤k ≠0 Δ zero ∷ ys) =
    ⊞-match (j≤k ∺ i≤k) y xs ^ zero ∷↓ ys
  ⊞-inj i≤k xs (y Δ suc j ∷ ys) =
    xs Π i≤k ^ zero ∷↓ y Δ j ∷ ys

  ⊞-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
  ⊞-coeffs [] ys = ys
  ⊞-coeffs (x Δ i ∷ xs) = ⊞-zip-r x i xs

  ⊞-zip : ∀ {p q n}
        → ℕ.Ordering p q
        → Coeff n
        → Coeffs n
        → Coeff n
        → Coeffs n
        → Coeffs n
  ⊞-zip (ℕ.less    i k) x xs y ys = x Δ i ∷ ⊞-zip-r y k ys xs
  ⊞-zip (ℕ.greater j k) x xs y ys = y Δ j ∷ ⊞-zip-r x k xs ys
  ⊞-zip (ℕ.equal   i  ) (x ≠0) xs (y ≠0) ys =
    (x ⊞ y) ^ i ∷↓ ⊞-coeffs xs ys

  ⊞-zip-r : ∀ {n} → Coeff n → ℕ → Coeffs n → Coeffs n → Coeffs n
  ⊞-zip-r x i xs [] = x Δ i ∷ xs
  ⊞-zip-r x i xs (y Δ j ∷ ys) = ⊞-zip (ℕ.compare i j) x xs y ys

----------------------------------------------------------------------
-- Negation
----------------------------------------------------------------------

mutual
  ⊟_ : ∀ {n} → Poly n → Poly n
  ⊟_ (Κ x  Π i≤n) = Κ (- x) Π i≤n
  ⊟_ (Σ xs Π i≤n) = ⊟-coeffs xs Π↓ i≤n

  ⊟-coeffs : ∀ {n} → Coeffs n → Coeffs n
  ⊟-coeffs (x ≠0 Δ i  ∷ xs) = ⊟ x ^ i ∷↓ ⊟-coeffs xs
  ⊟-coeffs [] = []

----------------------------------------------------------------------
-- Multiplication
----------------------------------------------------------------------
mutual
  infixl 7 _⊠_
  _⊠_ : ∀ {n} → Poly n → Poly n → Poly n
  (xs Π i≤n) ⊠ (ys Π j≤n) = ⊠-match (i≤n ∺ j≤n) xs ys

  ⊠-inj : ∀ {i k}
        → i ≤ k
        → FlatPoly i
        → Coeffs k
        → Coeffs k
  ⊠-inj _ _ [] = []
  ⊠-inj i≤k x (y Π j≤k ≠0 Δ p ∷ ys) =
    ⊠-match (i≤k ∺ j≤k) x y ^ p ∷↓ ⊠-inj i≤k x ys

  ⊠-match : ∀ {i j n}
          → {i≤n : i ≤ n}
          → {j≤n : j ≤ n}
          → Ordering i≤n j≤n
          → FlatPoly i
          → FlatPoly j
          → Poly n
  ⊠-match (eq i&j≤n) (Κ x)  (Κ y)  = Κ (x * y)         Π  i&j≤n
  ⊠-match (eq i&j≤n) (Σ xs) (Σ ys) = ⊠-coeffs xs ys    Π↓ i&j≤n
  ⊠-match (i≤j-1 < j≤n) xs (Σ ys) = ⊠-inj i≤j-1 xs ys Π↓ j≤n
  ⊠-match (i≤n > j≤i-1) (Σ xs) ys = ⊠-inj j≤i-1 ys xs Π↓ i≤n

  -- A simple shift-and-add algorithm.
  ⊠-coeffs : ∀ {n} → Coeffs n → Coeffs n → Coeffs n
  ⊠-coeffs _ [] = []
  ⊠-coeffs xs (y ≠0 Δ j ∷ ys) = ⊠-step y ys xs ⍓ j

  ⊠-step : ∀ {n} → Poly n → Coeffs n → Coeffs n → Coeffs n
  ⊠-step y ys [] = []
  ⊠-step y ys (x Π j≤n ≠0 Δ i ∷ xs) =
    (x Π j≤n) ⊠ y ^ i ∷↓ ⊞-coeffs (⊠-inj j≤n x ys) (⊠-step y ys xs)

----------------------------------------------------------------------
-- Constants and Variables
----------------------------------------------------------------------

-- The constant polynomial
κ : ∀ {n} → Carrier → Poly n
κ x = Κ x Π z≤n

-- A variable
ι : ∀ {n} → Fin n → Poly n
ι i = (κ 1# ^ 1 ∷↓ []) Π↓ Fin⇒≤ i
