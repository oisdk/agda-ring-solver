{-# OPTIONS --without-K #-}

module Positional.Binary where

open import Data.List as List using (List; []; _∷_; foldr)
open import Data.Nat as ℕ using (ℕ; zero; suc; compare; Ordering; less; equal; greater)
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

-- A list of zero runs.
--
-- 0  = []
-- 52 = 001011 = [2,1,0]
-- 4  = 001    = [2]
-- 5  = 101    = [0,1]
-- 10 = 0101   = [1,1]
Bin : Set
Bin = List ℕ

incr′ : ℕ → Bin → Bin
incr′ i [] = i ∷ []
incr′ i (suc x ∷ xs) = i ∷ x ∷ xs
incr′ i (zero ∷ xs) = incr′ (suc i) xs

incr : Bin → Bin
incr = incr′ 0

infixl 6 _+_
_+_ : Bin → Bin → Bin
[] + ys = ys
(x ∷ xs) + ys = +-zip-r x xs ys
  where
  +-zip : ∀ {x y} → Ordering x y → Bin → Bin → Bin
  +-zip-r : ℕ → Bin → Bin → Bin
  +-incr : ℕ → Bin → Bin → Bin
  +-incr-r : ℕ → Bin → ℕ → Bin → Bin
  +-incr-zip : ℕ → ∀ {i j} → Ordering i j → Bin → Bin → Bin
  incr″ : ℕ → ℕ → Bin → Bin

  +-zip (less    i k) xs ys = i ∷ +-zip-r k ys xs
  +-zip (equal   k  ) xs ys = +-incr (suc k) xs ys
  +-zip (greater j k) xs ys = j ∷ +-zip-r k xs ys

  +-zip-r x xs [] = x ∷ xs
  +-zip-r x xs (y ∷ ys) = +-zip (compare x y) xs ys

  incr″ i zero xs = incr′ (suc i) xs
  incr″ i (suc x) xs = i ∷ x ∷ xs

  +-incr i [] ys = incr′ i ys
  +-incr i (x ∷ xs) ys = +-incr-r i ys x xs

  +-incr-r i [] x xs = incr″ i x xs
  +-incr-r i (y ∷ ys) x xs = +-incr-zip i (compare y x) ys xs

  +-incr-zip c (less zero k) xs ys = +-incr-r (suc c) xs k ys
  +-incr-zip c (less (suc i) k) xs ys = c ∷ i ∷ +-zip-r k ys xs
  +-incr-zip c (greater zero k) xs ys = +-incr-r (suc c) ys k xs
  +-incr-zip c (greater (suc j) k) xs ys = c ∷ j ∷ +-zip-r k xs ys
  +-incr-zip c (equal   k  ) xs ys = c ∷ +-incr k xs ys

pow : ℕ → Bin → Bin
pow i [] = []
pow i (x ∷ xs) = (x ℕ.+ i) ∷ xs

infixl 7 _*_
_*_ : Bin → Bin → Bin
_*_ [] _ = []
_*_ (x ∷ xs) = pow x ∘ foldr (λ y ys → y ∷ xs + ys) []

fromNat : ℕ → Bin
fromNat zero = []
fromNat (suc n) = incr (fromNat n)

infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ suc y = x ℕ.* (x ^ y)

toNat : Bin → ℕ
toNat = List.foldr (λ x xs → (2 ^ x) ℕ.* suc (2 ℕ.* xs)) 0


private

  testLimit : ℕ
  testLimit = 25

  nats : List ℕ
  nats = List.downFrom testLimit

  natPairs : List (ℕ × ℕ)
  natPairs = List.concatMap (λ x → List.map (x ,_) nats) nats

  _=[_]_ : (ℕ → ℕ) → List ℕ → (Bin → Bin) → Set
  f =[ ns ] g = List.map f ns ≡ List.map (toNat ∘ g ∘ fromNat) ns

  _=[_]₂_ : (ℕ → ℕ → ℕ) → List (ℕ × ℕ) → (Bin → Bin → Bin) → Set
  f =[ ps ]₂ g =
    List.map (uncurry f) ps ≡ List.map (toNat ∘ uncurry (g on fromNat)) ps

-- And then the tests:

private

  test-+ : ℕ._+_ =[ natPairs ]₂ _+_
  test-+ = refl

  test-* : ℕ._*_ =[ natPairs ]₂ _*_
  test-* = refl

  test-suc : suc =[ nats ] incr
  test-suc = refl

  test-downFrom : List.map (toNat ∘ fromNat) (List.downFrom testLimit) ≡
                  List.downFrom testLimit
  test-downFrom = refl
