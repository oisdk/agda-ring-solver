module Positional.PAdic where

open import Modular renaming (_+_ to _M+_; -_ to M-_; _*_ to _M*_; incr to incr-m)
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
  head (neg [ d ∣ s≥m p≥d ] ys) = M- [ suc d ∣ p≥d ]
  tail (neg [ d ∣ s≥m p≥d ] ys) = map M-_ ys

open import Data.Bool
open import Data.Product hiding (map)
open import Function

_+_ : ∀ {n i} → ℤ {i} n → ℤ {i} n → ℤ {i} n
_+_ {n} xs ys = mapAccumL f false ⦇ xs M+ ys ⦈
  where
  f : Bool → Mod n × Bool → Mod n × Bool
  f false = id
  f true (x , c) with incr-m x
  f true (x , c) | y , c′ = y , c ∨ c′

incr : ∀ {n i} → ℤ {i} n → ℤ {i} n
incr {n} xs = go (incr-m (head xs)) (tail xs)
  where
  go : ∀ {i} → Mod n × Bool → (∀ {j : Size< i} → ℤ {j} n) → ℤ {i} n
  head (go (y , c) ys) = y
  tail (go (y , false) ys) = ys
  tail (go (y , true) ys) = incr ys

addSing : ∀ {n i} → Mod n → ℤ {i} n → ℤ {i} n
addSing {n} x xs = go (x M+ head xs) (tail xs)
  where
  go : ∀ {i} → Mod n × Bool → (∀ {j : Size< i} → ℤ {j} n) → ℤ {i} n
  head (go (y , c) ys) = y
  tail (go (y , false) ys) = ys
  tail (go (y , true) ys) = incr ys

carry : ∀ {n i} → Stream {i} (Mod n × Mod n) → ℤ {i} n
head (carry xs) = proj₁ (head xs)
tail (carry xs) = addSing (proj₂ (head xs)) (carry (tail xs))

_*_ : ∀ {n i} → ℤ {i} n → ℤ {i} n → ℤ {i} n
_*_ {n} xs′ = go (head xs′) (tail xs′)
  where
  go : ∀ {i} → Mod n → (∀ {j : Size< i} → ℤ {j} n) → ℤ {i} n → ℤ {i} n
  go {i} x xs ys = go′ (x M* head ys)
    where
    go′ : Mod n × Mod n → ℤ {i} n
    head (go′ (s , c)) = s
    tail (go′ (s , c)) = addSing c (carry (map (_M* head ys) xs) + go x xs (tail ys))
