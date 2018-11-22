{-# OPTIONS --without-K --safe #-}

module Examples where

open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.Reflection
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties

NatRing : AlmostCommutativeRing _ _
NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_

open AlmostCommutativeRing NatRing

lemma : ∀ w x y z → (w * 1000) + (y + x + z) * 10000 ≈ 10000 * (z + x + y) + (1000 * w)
lemma = solve NatRing
