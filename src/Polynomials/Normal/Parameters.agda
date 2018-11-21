{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Unary
open import Level
open import Algebra.Solver.Ring.AlmostCommutativeRing

module Polynomials.Normal.Parameters where

-- This record stores all the stuff we need for the coefficients:
--
--  * A raw ring
--  * A (decidable) predicate on "zeroeness"
--
-- It's used for defining the operations on the horner normal form.
record RawCoeff ℓ₁ ℓ₂ : Set (suc (ℓ₁ ⊔ ℓ₂)) where
  field
    coeffs  : RawRing ℓ₁
    Zero-C  : Pred (RawRing.Carrier coeffs) ℓ₂
    zero-c? : Decidable Zero-C

  open RawRing coeffs public

-- This record stores the full information we need for converting
-- to the final ring.
record Homomorphism ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Set (suc (ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₄)) where
  field
    coeffs : RawCoeff ℓ₁ ℓ₂
  module Raw = RawCoeff coeffs
  field
    ring     : AlmostCommutativeRing ℓ₃ ℓ₄
    morphism : Raw.coeffs -Raw-AlmostCommutative⟶ ring
  open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧ᵣ) public
  open AlmostCommutativeRing ring public
  field
    Zero-C⟶Zero-R : ∀ x → Raw.Zero-C x → ⟦ x ⟧ᵣ ≈ 0#

