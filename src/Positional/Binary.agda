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
⟦_⟧ = List.foldr (λ x xs → (1 ℕ.+ xs ℕ.* 2) ℕ.* 2 ^ x) 0

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
  +-ne (ℕ.equal   k  ) xs ys = suc k ∷ shiftl (xs + ys)
  +-ne (ℕ.greater j k) xs ys = j ∷ +-ne-l k ys xs

  +-ne-l : ℕ → Bin → Bin → Bin
  +-ne-l k [] ys = k ∷ ys
  +-ne-l k (x ∷ xs) ys = +-ne (ℕ.compare x k) xs ys

  shiftl : Bin → Bin
  shiftl [] = []
  shiftl (zero ∷ xs) = 1 ∷ shiftl xs
  shiftl (suc x ∷ xs) = x ∷ xs

infixl 7 _*_
_*_ : Bin → Bin → Bin
[] * ys = []
(x ∷ xs) * [] = []
(x ∷ xs) * (y ∷ ys) = y ℕ.+ x ∷ ys + xs * (0 ∷ ys)
