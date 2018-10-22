module Positional.PAdic.Ball where

open import Positional.PAdic as Expansion using (ℤ; 0ₚ)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Vec using (Vec; []; _∷_)
open import Modular as Mod using (Mod)
open import Data.Stream
open Stream

Ball : ℕ → ℕ → Set
Ball p = Vec (Mod p)

truncate : ∀ {p n} → ℤ p → Ball p n
truncate = takeVec _

expand : ∀ {p n} → Ball p n → ℤ p → ℤ p
expand [] ys = ys
head (expand (x ∷ xs) ys) = x
tail (expand (x ∷ xs) ys) = expand xs ys

_⊣_⊢_ : ∀ {p n} → Ball p n → (ℤ p → ℤ p → ℤ p) → Ball p n → Ball p n
xs ⊣ _*_ ⊢ ys = truncate (expand xs 0ₚ * expand ys 0ₚ)

infixl 6 _+_
_+_ : ∀ {p n} → Ball p n → Ball p n → Ball p n
xs + ys = xs ⊣ Expansion._+_ ⊢ ys

infixl 7 _*_
_*_ :  ∀ {p n} → Ball p n → Ball p n → Ball p n
xs * ys = xs ⊣ Expansion._*_ ⊢ ys

-_ : ∀ {p n} → Ball p n → Ball p n
- xs = truncate (Expansion.negate (expand xs 0ₚ))
