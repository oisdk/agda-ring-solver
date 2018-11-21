{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Polynomials.Normal.Parameters

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Homomorphism
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Polynomials.Homomorphism.Addition homo
  using (⊞-hom)
  public

open import Polynomials.Homomorphism.Multiplication homo
  using (⊠-hom)
  public

open import Polynomials.Homomorphism.Negation homo
  using (⊟-hom)
  public

open import Polynomials.Homomorphism.Semantics homo
  using (κ-hom; ι-hom)
  public
