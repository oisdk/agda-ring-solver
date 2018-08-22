{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Ring.Homomorphism
  {r₁ r₂ r₃ r₄}
  (coeff : RawRing r₁)
  (Zero-C : Pred (RawRing.Carrier coeff) r₂)
  (zero-c? : Decidable Zero-C)
  (ring : AlmostCommutativeRing r₃ r₄)
  (morphism : coeff -Raw-AlmostCommutative⟶ ring)
  (Zero-C⟶Zero-R : ∀ x → Zero-C x → AlmostCommutativeRing._≈_ ring (_-Raw-AlmostCommutative⟶_.⟦_⟧ morphism x) (AlmostCommutativeRing.0# ring))
  where

open import Polynomials.Ring.Homomorphism.Addition coeff Zero-C zero-c? ring morphism Zero-C⟶Zero-R
  using (⊞-hom)
  public

open import Polynomials.Ring.Homomorphism.Multiplication coeff Zero-C zero-c? ring morphism Zero-C⟶Zero-R
  using (⊠-hom)
  public

open import Polynomials.Ring.Homomorphism.Negation coeff Zero-C zero-c? ring morphism Zero-C⟶Zero-R
  using (⊟-hom)
  public

open import Polynomials.Ring.Homomorphism.Semantics coeff Zero-C zero-c? ring morphism Zero-C⟶Zero-R
  using (κ-hom; ι-hom)
  public
