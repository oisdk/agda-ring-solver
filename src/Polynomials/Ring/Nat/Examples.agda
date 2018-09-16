{-# OPTIONS --without-K #-}

module Polynomials.Ring.Nat.Examples where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Polynomials.Ring.Simple.AlmostCommutativeRing
NatRing : AlmostCommutativeRing _ _
NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_
open AlmostCommutativeRing NatRing
open import Polynomials.Ring.Simple.Reflection

mmmm : (x y : ℕ) → x + y * 1 + 3 ≈ 2 + 1 + x + y
mmmm = solve NatRing

mmm : ∀ x → 1 + x ≈ x + 1
mmm = solve NatRing
