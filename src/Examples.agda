module Examples where

open import Agda.Builtin.FromNat
open import Data.Nat using (ℕ)
open import Data.Integer using (ℤ)

instance
  numberNat : Number ℕ
  numberNat = Data.Nat.Literals.number
    where import Data.Nat.Literals

instance
  numberInt : Number ℤ
  numberInt = Data.Integer.Literals.number
    where import Data.Integer.Literals

open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.AlmostCommutativeRing.Instances
open import Polynomial.Simple.Reflection

module NatExamples where
  open AlmostCommutativeRing Nat.ring

  lemma : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
  lemma = solve Nat.ring

module IntExamples where
  open AlmostCommutativeRing Int.ring

  lemma : ∀ x y → x + y * 1 + 3 ≈ 3 + 1 + y + x + - 1
  lemma = solve Int.ring
