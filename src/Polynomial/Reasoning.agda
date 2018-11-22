{-# OPTIONS --without-K --safe #-}

open import Algebra.Solver.Ring.AlmostCommutativeRing

-- Some specialised tools for equaltional reasoning.
module Polynomial.Reasoning
  {a ℓ}
  (ring : AlmostCommutativeRing a ℓ)
  where

open AlmostCommutativeRing ring
open import Relation.Binary.EqReasoning setoid public

infixr 1 ≪+_ +≫_ ≪*_ *≫_
≪+_ : ∀ {x₁ x₂ y} → x₁ ≈ x₂ → x₁ + y ≈ x₂ + y
≪+ prf = +-cong prf refl

+≫_ : ∀ {x y₁ y₂} → y₁ ≈ y₂ → x + y₁ ≈ x + y₂
+≫_ = +-cong refl

≪*_ : ∀ {x₁ x₂ y} → x₁ ≈ x₂ → x₁ * y ≈ x₂ * y
≪* prf = *-cong prf refl

*≫_ : ∀ {x y₁ y₂} → y₁ ≈ y₂ → x * y₁ ≈ x * y₂
*≫_ = *-cong refl

-- transitivity as an operator
infixr 0 _⊙_
_⊙_ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
_⊙_ = trans
