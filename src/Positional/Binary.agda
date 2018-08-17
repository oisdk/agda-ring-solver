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

⟦_⟧ : Bin → ℕ
⟦_⟧ = List.foldr (λ x xs → (2 ^ x) ℕ.* suc (2 ℕ.* xs)) 0

incr′ : Bin → ℕ × Bin
incr′ [] = 0 , []
incr′ (suc x ∷ xs) = 0 , x ∷ xs
incr′ (zero ∷ xs) = map₁ suc (incr′ xs)

incr : Bin → Bin
incr = uncurry _∷_ ∘ incr′

fromNat : ℕ → Bin
fromNat zero = []
fromNat (suc n) = incr (fromNat n)

mutual
  infixl 6 _+_
  _+_ : Bin → Bin → Bin
  [] + ys = ys
  (x ∷ xs) + [] = x ∷ xs
  (x ∷ xs) + (y ∷ ys) = +-ne (ℕ.compare x y) xs ys

  +-ne : ∀ {x y} → ℕ.Ordering x y → Bin → Bin → Bin
  +-ne (ℕ.less    i k) xs ys = i ∷ +-ne-l k xs ys
  +-ne (ℕ.equal   k  ) xs ys = suc k ∷↓ (xs + ys)
  +-ne (ℕ.greater j k) xs ys = j ∷ +-ne-l k ys xs

  +-ne-l : ℕ → Bin → Bin → Bin
  +-ne-l k [] ys = k ∷ ys
  +-ne-l k (x ∷ xs) ys = +-ne (ℕ.compare x k) xs ys

  _∷↓_ : ℕ → Bin → Bin
  x ∷↓ xs = uncurry (_∷_ ∘ (x ℕ.+_)) (incr′ xs)

infixl 7 _*_
_*_ : Bin → Bin → Bin
[] * ys = []
(x ∷ xs) * [] = []
(x ∷ xs) * (y ∷ ys) = y ℕ.+ x ∷ ys + xs * (0 ∷ ys)

private

  testLimit : ℕ
  testLimit = 25

  nats : List ℕ
  nats = List.downFrom testLimit

  natPairs : List (ℕ × ℕ)
  natPairs = List.concatMap (λ x → List.map (x ,_) nats) nats

  _=[_]_ : (ℕ → ℕ) → List ℕ → (Bin → Bin) → Set
  f =[ ns ] g = List.map f ns ≡ List.map (⟦_⟧ ∘ g ∘ fromNat) ns

  _=[_]₂_ : (ℕ → ℕ → ℕ) → List (ℕ × ℕ) → (Bin → Bin → Bin) → Set
  f =[ ps ]₂ g =
    List.map (uncurry f) ps ≡ List.map (⟦_⟧ ∘ uncurry (g on fromNat)) ps

-- And then the tests:

private

  test-+ : ℕ._+_ =[ natPairs ]₂ _+_
  test-+ = refl

  test-* : ℕ._*_ =[ natPairs ]₂ _*_
  test-* = refl

  test-suc : suc =[ nats ] incr
  test-suc = refl

  test-downFrom : List.map (⟦_⟧ ∘ fromNat) (List.downFrom testLimit) ≡
                  List.downFrom testLimit
  test-downFrom = refl
