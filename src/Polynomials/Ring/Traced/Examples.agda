{-# OPTIONS --without-K #-}

module Polynomials.Ring.Traced.Examples where

import Algebra.Solver.Ring.AlmostCommutativeRing as ACR
import Level
open import Algebra.Ring.Traced
open import Function
open import Data.Empty
open ACR.AlmostCommutativeRing ring
open import Relation.Nullary
import Polynomials.Ring.Expr
  rawRing
  (const ⊥)
  (λ x → no (λ z → z))
  ring
  (ACR.-raw-almostCommutative⟶ ring)
  (λ x ())
  as Solver

lem3 : (x : Expr) → (κ 2 * (x + κ 4) ≡⋯≡ κ 8 + κ 2 * x)
lem3 = Solver.solve 1 (λ x' → Solver.Κ (κ 2) Solver.⊗ (x' Solver.⊕ Solver.Κ (κ 4)) Solver.⊜ Solver.Κ (κ 8) Solver.⊕ Solver.Κ (κ 2) Solver.⊗ x') (_ ≡⟨ "a" ⟩ [refl])

example = lem3 (ι "x")
