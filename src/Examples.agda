{-# OPTIONS --without-K #-}

module Examples where

open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.Reflection
open import Agda.Builtin.FromNat
open Number {{...}} public

open import Data.Nat as ℕ using (ℕ)
import Data.Nat.Literals
open import Data.Integer as ℤ using (ℤ)
import Data.Integer.Literals

instance
  NatLit : Number ℕ
  NatLit = Data.Nat.Literals.number

instance
  IntLit : Number ℤ
  IntLit = Data.Integer.Literals.number

module Nat where
  open import Data.Nat.Properties

  NatRing : AlmostCommutativeRing _ _
  NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_

  open AlmostCommutativeRing NatRing

  lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + x + y
  lemma₁ = solve NatRing

  lemma₂ : ∀ x y z → x * y + z ≈ z + y * x
  lemma₂ = solve NatRing

module Int where
  open import Data.Integer.Properties

  IntRing : AlmostCommutativeRing _ _
  IntRing = fromCommutativeRing +-*-commutativeRing ℤ._≟_

  open AlmostCommutativeRing IntRing

  lemma₃ : ∀ x → x + - x ≈ 0
  lemma₃ = solve IntRing

  lemma₄ : ∀ x y → y + y * - 1 ≈ (x + x) + - (x * 2)
  lemma₄ = solve IntRing

