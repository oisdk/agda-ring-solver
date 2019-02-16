{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Data.Nat as ℕ using (ℕ; suc; zero)

module Polynomial.Exponentiation {ℓ} (ring : RawRing ℓ) where

open RawRing ring

infixr 8 _^_+1
_^_+1 : Carrier → ℕ → Carrier
x ^ zero  +1 = x
x ^ suc n +1 = (x ^ n +1) * x

infixr 8 _^_
_^_ : Carrier → ℕ → Carrier
x ^ zero  = 1#
x ^ suc i = x ^ i +1
{-# INLINE _^_ #-}
