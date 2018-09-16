{-# OPTIONS --without-K #-}

module Polynomials.Ring.Nat.Examples where

open import Data.Nat as ℕ using (ℕ)
open import Data.Nat.Properties
open import Polynomials.Ring.Simple.AlmostCommutativeRing
NatRing : AlmostCommutativeRing _ _
NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_
open AlmostCommutativeRing NatRing
open import Polynomials.Ring.Simple.Reflection

lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + x + y
lemma₁ = solve NatRing

lemma₂ : ∀ x y z → x * y + z ≈ z + y * x
lemma₂ = solve NatRing
