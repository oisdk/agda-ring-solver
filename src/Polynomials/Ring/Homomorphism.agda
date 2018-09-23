{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Polynomials.Ring.Normal.Parameters

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Ring.Homomorphism
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Polynomials.Ring.Homomorphism.Addition homo
  using (⊞-hom)
  public

open import Polynomials.Ring.Homomorphism.Multiplication homo
  using (⊠-hom)
  public

open import Polynomials.Ring.Homomorphism.Negation homo
  using (⊟-hom)
  public

open import Polynomials.Ring.Homomorphism.Semantics homo
  using (κ-hom; ι-hom)
  public
