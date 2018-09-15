{-# OPTIONS --without-K #-}

module Polynomials.Ring.Nat.Examples where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
import Level
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
NatRing : ACR.AlmostCommutativeRing Level.zero Level.zero
NatRing = ACR.fromCommutativeSemiring *-+-commutativeSemiring
open ACR.AlmostCommutativeRing NatRing
open import Polynomials.Ring.Reflection NatRing ℕ._≟_
open import Function
open import Reflection
import Data.Fin as Fin
open import Data.Product

lem3 : Set
lem3 = (x : ℕ) → 0 + x ≡ x

ex3 : Term
ex3 = quoteTerm ((Expr ℕ 0 × Expr ℕ 0) ∋ (Κ 1# ⊕ Κ 1# , Κ 1#))

ex4 : Term
ex4 = quoteTerm (∀ x → x + 1# ≈ x + 1#)

num : ℕ
num = 4

ex5 : Expr ℕ ℕ.zero
ex5 = qExpr (1# + num * 3)

lem5 : ∀ x y z → z + (x + y) ≈ x + 0 + 0 + z + 0 + y
lem5 = solve 3 (qEquiv (((x y z : ℕ) → z + (x + y) ≈ x + 0 + 0 + z + 0 + y))) refl
