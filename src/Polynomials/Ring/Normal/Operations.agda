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
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Function
open import Data.Fin as Fin using (Fin)
open import Data.Nat.Order.Compare using (compare)

-- Multivariate polynomials.
module Polynomials.Ring.Normal.Operations
  {a ℓ}
  (coeffs : RawRing a)
  (Zero-C : Pred (RawRing.Carrier coeffs) ℓ)
  (zero-c? : Decidable Zero-C)
  where

open import Polynomials.Ring.Normal.Definition coeffs Zero-C zero-c?
open import Data.Nat.Order.Gappy
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
-- number of variables in the tail: like repeatedly taking the length of
-- the tail of a list, it's quadratic.
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
-- infix 4 _≤_
-- data _≤_ (m : ℕ) : ℕ → Set where
--   m≤m : m ≤ m
--   ≤-s : ∀ {n} → (m≤n : m ≤ n) → m ≤ suc n
--
-- (This is a rewritten version of _≤′_ from Data.Nat.Base).
--
-- While this structure stores the same information as ≤, it does so
-- by induction on the *gap*. This became apparent when I realised you
-- could use it to write a comparison function which was linear in the
-- size of the gap (even though it was comparing the length of the
-- tail):

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
-- 1. The ≤-compare function is one of those reassuring ones for which
--    Agda can completely fill in the type for me.
-- 2. This function looks somewhat similar to the one for comparing ℕ
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
-- Trying to prove this convinced me that it might not even be possible
-- without K. On top of that, I also noticed that I would need to
-- prove things like:
--
--   ∀ {i j n}
--   → (i≤j : i ≤ j)
--   → (j≤n : j ≤ n)
--   → (x : FlatPoly i)
--   → (Ρ : Vec Carrier n)
--   → ⟦ x Π (i≤j ⋈ j≤n) ⟧ Ρ ≈ ⟦ x Π i≤j ⟧ (drop j≤n Ρ)
--
-- ⋈ is transitivity, defined as:
-- _⋈_ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
-- xs ⋈ m≤m = xs
-- xs ⋈ (≤-s ys) = ≤-s (xs ⋈ ys)
--
-- Effectively, I needed to prove that transitivity was a
-- homomorphism.
--
-- I realised that I had not run into these difficulties with the
-- comparison function I was using for the exponent gaps: why? Well
-- that function provides a proof about its *arguments* whereas the
-- one I wrote above only provides a proof about the i and j.
--
-- data Ordering : Rel ℕ 0ℓ where
--   less    : ∀ m k → Ordering m (suc (m + k))
--   equal   : ∀ m   → Ordering m m
--   greater : ∀ m k → Ordering (suc (m + k)) m
--
-- If I tried to mimick the above as closely as possible, I would also
-- need an analogue to +: of course this was ⋈, so I was going to get
-- my transitivity proof as well as everything else. The result is the
-- following:
-- data Ordering {n : ℕ} : ∀ {i j}
--                       → (i≤n : i ≤ n)
--                       → (j≤n : j ≤ n)
--                       → Set
--                       where
--   _<_ : ∀ {i j-1}
--       → (i≤j-1 : i ≤ j-1)
--       → (j≤n : suc j-1 ≤ n)
--       → Ordering (≤-s i≤j-1 ⋈ j≤n) j≤n
--   _>_ : ∀ {i-1 j}
--       → (i≤n : suc i-1 ≤ n)
--       → (j≤i-1 : j ≤ i-1)
--       → Ordering i≤n (≤-s j≤i-1 ⋈ i≤n)
--   eq : ∀ {i} → (i≤n : i ≤ n) → Ordering i≤n i≤n

-- _cmp_ : ∀ {i j n}
--     → (x : i ≤ n)
--     → (y : j ≤ n)
--     → Ordering x y
-- m≤m cmp m≤m = eq m≤m
-- m≤m cmp ≤-s y = m≤m > y
-- ≤-s x cmp m≤m = x < m≤m
-- ≤-s x cmp ≤-s y with x cmp y
-- ≤-s .(≤-s i≤j-1 ⋈ y) cmp ≤-s y            | i≤j-1 < .y = i≤j-1 < ≤-s y
-- ≤-s x            cmp ≤-s .(≤-s j≤i-1 ⋈ x) | .x > j≤i-1 = ≤-s x > j≤i-1
-- ≤-s x            cmp ≤-s .x               | eq .x = eq (≤-s x)

-- z≤n : ∀ {n} → zero ≤ n
-- z≤n {zero} = m≤m
-- z≤n {suc n} = ≤-s z≤n
open RawRing coeffs

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
    ⊞-match (j≤k cmp i≤k) y xs ^ zero ∷↓ ys
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
  ⊞-zip-r x i xs (y Δ j ∷ ys) = ⊞-zip (compare i j) x xs y ys

----------------------------------------------------------------------
-- Negation
----------------------------------------------------------------------

open import Induction.Nat
open import Induction.WellFounded

⌊_⌋ : ℕ → Set
⌊_⌋ = Acc ℕ._<′_

⌊↓⌋ : ∀ {n} → ⌊ n ⌋
⌊↓⌋ {n} = <′-wellFounded n

-- recurse on acc directly
-- https://github.com/agda/agda/issues/3190#issuecomment-416900716

mutual
  ⊟-step : ∀ {n} → ⌊ n ⌋ → Poly n → Poly n
  ⊟-step _        (Κ x  Π i≤n) = Κ (- x) Π i≤n
  ⊟-step (acc wf) (Σ xs Π i≤n) =
    foldr (⊟-cons (wf _ i≤n)) [] xs Π↓ i≤n

  ⊟-cons : ∀ {n} → ⌊ n ⌋ → CoeffExp n → Coeffs n → Coeffs n
  ⊟-cons ac (x ≠0 Δ i) xs = ⊟-step ac x ^ i ∷↓ xs

⊟_ : ∀ {n} → Poly n → Poly n
⊟_ = ⊟-step ⌊↓⌋

----------------------------------------------------------------------
-- Multiplication
----------------------------------------------------------------------
mutual
  ⊠-step : ∀ {n} → ⌊ n ⌋ → Poly n → Poly n → Poly n
  ⊠-step a (xs Π i≤n) (ys Π j≤n) = ⊠-match a (i≤n cmp j≤n) xs ys

  ⊠-inj : ∀ {i k}
        → ⌊ k ⌋
        → i ≤ k
        → FlatPoly i
        → CoeffExp k
        → Coeffs k
        → Coeffs k
  ⊠-inj a i≤k x (y Π j≤k ≠0 Δ p) ys =
    ⊠-match a (i≤k cmp j≤k) x y ^ p ∷↓ ys

  ⊠-match : ∀ {i j n}
          → ⌊ n ⌋
          → {i≤n : i ≤ n}
          → {j≤n : j ≤ n}
          → Ordering i≤n j≤n
          → FlatPoly i
          → FlatPoly j
          → Poly n
  ⊠-match _ (eq i&j≤n)        (Κ  x) (Κ  y) = Κ (x * y)                               Π  i&j≤n
  ⊠-match (acc wf) (eq i&j≤n) (Σ xs) (Σ ys) = ⊠-coeffs (wf _ i&j≤n) xs ys             Π↓ i&j≤n
  ⊠-match (acc wf) (i≤j-1 < j≤n) xs (Σ ys)  = foldr (⊠-inj (wf _ j≤n) i≤j-1 xs) [] ys Π↓ j≤n
  ⊠-match (acc wf) (i≤n > j≤i-1) (Σ xs) ys  = foldr (⊠-inj (wf _ i≤n) j≤i-1 ys) [] xs Π↓ i≤n

  -- A simple shift-and-add algorithm.
  ⊠-coeffs : ∀ {n} → ⌊ n ⌋ → Coeffs n → Coeffs n → Coeffs n
  ⊠-coeffs _ _ [] = []
  ⊠-coeffs a xs (y ≠0 Δ j ∷ ys) = foldr (⊠-cons a y ys) [] xs ⍓ j

  ⊠-cons : ∀ {n}
         → ⌊ n ⌋
         → Poly n
         → Coeffs n
         → CoeffExp n
         → Coeffs n
         → Coeffs n
  ⊠-cons a y ys (x Π j≤n ≠0 Δ i) xs =
    ⊠-step a (x Π j≤n) y ^ i ∷↓ ⊞-coeffs (foldr (⊠-inj a j≤n x) [] ys) xs

infixl 7 _⊠_
_⊠_ : ∀ {n} → Poly n → Poly n → Poly n
_⊠_ = ⊠-step ⌊↓⌋

----------------------------------------------------------------------
-- Constants and Variables
----------------------------------------------------------------------

-- The constant polynomial
κ : ∀ {n} → Carrier → Poly n
κ x = Κ x Π z≤n

-- A variable
ι : ∀ {n} → Fin n → Poly n
ι i = (κ 1# ^ 1 ∷↓ []) Π↓ Fin⇒≤ i
