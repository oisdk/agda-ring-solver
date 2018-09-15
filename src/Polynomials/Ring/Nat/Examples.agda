{-# OPTIONS --without-K #-}

module Polynomials.Ring.Nat.Examples where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Algebra.Solver.Ring.AlmostCommutativeRing
NatRing : AlmostCommutativeRing _ _
NatRing = fromCommutativeSemiring *-+-commutativeSemiring
open AlmostCommutativeRing NatRing
open import Polynomials.Ring.Reflection NatRing ℕ._≟_

lem : _
lem = solve 3 (makeGoal ((x y z : ℕ) → z + (x + y) ≈ x + 0 + 0 + z + 0 + y)) refl
