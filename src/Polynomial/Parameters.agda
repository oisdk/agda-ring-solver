{-# OPTIONS --without-K --safe #-}

-- This module packages up all the stuff that's passed to the other
-- modules in a convenient form.
module Polynomial.Parameters where

open import Function
open import Algebra
open import Relation.Unary
open import Level
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Data.Bool using (Bool; T)

-- This record stores all the stuff we need for the coefficients:
--
--  * A raw ring
--  * A (decidable) predicate on "zeroeness"
--
-- It's used for defining the operations on the horner normal form.
record RawCoeff c ℓ : Set (suc (c ⊔ ℓ)) where
  field
    coeffs  : RawRing c ℓ
    Zero-C  : RawRing.Carrier coeffs → Bool

  open RawRing coeffs public

-- This record stores the full information we need for converting
-- to the final ring.
record Homomorphism c ℓ₁ ℓ₂ ℓ₃ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃)) where
  field
    coeffs : RawCoeff c ℓ₁
  module Raw = RawCoeff coeffs
  field
    ring     : AlmostCommutativeRing ℓ₂ ℓ₃
    morphism : Raw.coeffs -Raw-AlmostCommutative⟶ ring
  open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧ᵣ) public
  open AlmostCommutativeRing ring public
  field
    Zero-C⟶Zero-R : ∀ x → T (Raw.Zero-C x) → 0# ≈  ⟦ x ⟧ᵣ
