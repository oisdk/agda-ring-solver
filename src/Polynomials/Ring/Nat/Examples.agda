{-# OPTIONS --without-K #-}
{-# OPTIONS --show-implicit #-}
{-# OPTIONS --verbose=5 #-}

module Polynomials.Ring.Nat.Examples where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
import Algebra.Solver.Ring.AlmostCommutativeRing as Complex
open import Polynomials.Ring.Simple.AlmostCommutativeRing
open import Data.Product

NatRing : AlmostCommutativeRing _ _
NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_

open AlmostCommutativeRing NatRing
open import Polynomials.Ring.Simple.Solver
open import Polynomials.Ring.Simple.Reflection


open import Reflection
open import Function

-- exampleExpr : Expr ℕ ℕ.zero
-- exampleExpr = qExpr (1 + (2 + 3))

lem :  Term
lem = quoteTerm (solve NatRing 3 (λ x y z → z ⊕ (x ⊕ y) , x ⊕ Κ 0 ⊕ Κ 0 ⊕ z ⊕ Κ 0 ⊕ y) refl)

mmmm : _
mmmm = solutionFor NatRing ((x y : ℕ) → x + y * 1 + 3 ≈ 2 + 1 + x + y)

mmm : ∀ x → 1 + x ≈ x + 1
mmm = trySolve NatRing
