module Examples where

open import Agda.Builtin.FromNat
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)

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

import Data.Nat.Show

open import Data.List as List using (List; _∷_; [])
open import Agda.Builtin.Nat using (_==_)
open import Relation.Traced Nat.ring _==_ Data.Nat.Show.show public
open AlmostCommutativeRing tracedRing
open import Data.String using (String; unlines)


lemma : ∀ x y → x + y * C 1 + C 3 ≈ C 2 + C 1 + y + x
lemma = solve tracedRing

explained : List String
explained = showProof (lemma (O (V "x")) (O (V "y")))

{-# DISPLAY V v = v #-}
{-# DISPLAY K x = x #-}
{-# DISPLAY O x = x #-}
