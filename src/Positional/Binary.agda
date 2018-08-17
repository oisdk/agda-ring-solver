module Positional.Binary where

open import Data.List as List using (List; []; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc)
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

infixr 8 _^_
_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ suc y = x ℕ.* (x ^ y)

toNat : Bin → ℕ
toNat = List.foldr (λ x xs → (2 ^ x) ℕ.* suc (2 ℕ.* xs)) 0

incr′ : ℕ → Bin → Bin
incr′ i [] = i ∷ []
incr′ i (suc x ∷ xs) = i ∷ x ∷ xs
incr′ i (zero ∷ xs) = incr′ (suc i) xs

incr : Bin → Bin
incr = incr′ 0

fromNat : ℕ → Bin
fromNat zero = []
fromNat (suc n) = incr (fromNat n)

infixl 6 _+_
_+_ : Bin → Bin → Bin
[] + ys = ys
(x ∷ xs) + [] = x ∷ xs
(x ∷ xs) + (y ∷ ys) = +-ne (ℕ.compare x y) xs ys
  where
  +-ne : ∀ {x y} → ℕ.Ordering x y → Bin → Bin → Bin
  +-ne-l : ℕ → Bin → Bin → Bin

  +-ne (ℕ.less    i k) xs ys = i ∷ +-ne-l k xs ys
  +-ne (ℕ.equal   k  ) xs ys = incr′ (suc k) (xs + ys)
  +-ne (ℕ.greater j k) xs ys = j ∷ +-ne-l k ys xs

  +-ne-l k [] = k ∷_
  +-ne-l k (x ∷ xs) = +-ne (ℕ.compare x k) xs

infixl 7 _*_
_*_ : Bin → Bin → Bin
[] * ys = []
(x ∷ xs) * [] = []
(x ∷ xs) * (y ∷ ys) = y ℕ.+ x ∷ ys + xs * (0 ∷ ys)

private

  testLimit : ℕ
  testLimit = 5

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
