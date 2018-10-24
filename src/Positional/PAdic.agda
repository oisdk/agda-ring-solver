module Positional.PAdic where

open import Modular as Mod using (Mod; [_∣_]; m≥m; s≥m; m≥0)
open import Data.Stream
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Agda.Builtin.Size

ℤ : {i : Size} → ℕ → Set
ℤ {i} p = Stream {i} (Mod p)

inf : ∀ {n} → Mod n → ℤ n
inf = pure

0ₚ : ∀ {n} → ℤ n
0ₚ = pure [ _ ∣ m≥m ]

-1ₚ : ∀ {n} → ℤ n
-1ₚ = pure [ _ ∣ m≥0 ]

open Stream

negate : ∀ {n i} → ℤ {i} n → ℤ {i} n
negate {n} xs = neg (head xs) (tail xs)
  where
  neg : ∀ {i} → Mod n → (∀ {j : Size< i} → ℤ {j} n)→ ℤ {i} n
  head (neg [ d ∣ m≥m ] ys) = [ d ∣ m≥m ]
  tail (neg [ d ∣ m≥m ] ys) = neg (head ys) (tail ys)
  head (neg [ d ∣ s≥m p≥d ] ys) = Mod.- [ suc d ∣ p≥d ]
  tail (neg [ d ∣ s≥m p≥d ] ys) = map Mod.-_ ys

open import Data.Bool
open import Data.Product hiding (map)
open import Function

infixl 6 _+_
_+_ : ∀ {n i} → ℤ {i} n → ℤ {i} n → ℤ {i} n
_+_ {n} xs ys = mapAccumL f false ⦇ xs Mod.+ ys ⦈
  where
  f : Bool → Mod n × Bool → Mod n × Bool
  f false x = x
  f true (x , c) = map₂ (c ∨_) (Mod.incr x)

incr : ∀ {n i} → ℤ {i} n → ℤ {i} n
incr {n} xs = go (Mod.incr (head xs)) (tail xs)
  where
  go : ∀ {i} → Mod n × Bool → (∀ {j : Size< i} → ℤ {j} n) → ℤ {i} n
  head (go (y , _    ) ys) = y
  tail (go (y , false) ys) = ys
  tail (go (y , true ) ys) = incr ys

infixl 6 _M+_
_M+_ : ∀ {n i} → Mod n → ℤ {i} n → ℤ {i} n
_M+_ {n} x xs = go (x Mod.+ head xs) (tail xs)
  where
  go : ∀ {i} → Mod n × Bool → (∀ {j : Size< i} → ℤ {j} n) → ℤ {i} n
  head (go (y , c) ys) = y
  tail (go (y , false) ys) = ys
  tail (go (y , true) ys) = incr ys

carry : ∀ {n i} → Stream {i} (Mod n × Mod n) → ℤ {i} n
head (carry xs) = proj₁ (head xs)
tail (carry xs) = proj₂ (head xs) M+ carry (tail xs)

infixl 7 _*M_
_*M_ : ∀ {n i} → ℤ {i} n → Mod n → ℤ {i} n
xs *M y = carry (map (Mod._* y) xs)

infixl 7 _*_
_*_ : ∀ {n i} → ℤ {i} n → ℤ {i} n → ℤ {i} n
_*_ {n} xs′ = go (head xs′) (tail xs′)
  where
  go : ∀ {i} → Mod n → (∀ {j : Size< i} → ℤ {j} n) → ℤ {i} n → ℤ {i} n
  go {i} x xs ys = go′ (x Mod.* head ys)
    where
    go′ : Mod n × Mod n → ℤ {i} n
    head (go′ (s , c)) = s
    tail (go′ (s , c)) = c M+ xs *M head ys + go x xs (tail ys)

module Interval where
  open import Data.List as List using (List; []; _∷_)
  open import Relation.Nullary

  Interval : ℕ → Set
  Interval n = List (Mod n × Mod n)

  commonPrefix : ∀ {n} → Interval n → List (Mod n) × Interval n
  commonPrefix [] = [] , []
  commonPrefix ((lb , ub) ∷ xs) with lb Mod.≟ ub
  commonPrefix ((lb , ub) ∷ xs) | yes p = map₁ (lb ∷_) (commonPrefix xs)
  commonPrefix xss@((lb , ub) ∷ xs) | no ¬p = [] , xss
