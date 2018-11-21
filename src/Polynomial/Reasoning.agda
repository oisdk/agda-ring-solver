{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary
open import Algebra.FunctionProperties
open import Algebra.Solver.Ring.AlmostCommutativeRing

-- Some specialised tools for equaltional reasoning.
module Polynomial.Reasoning
  {a ℓ}
  (ring : AlmostCommutativeRing a ℓ)
  where

open AlmostCommutativeRing ring
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Nullary
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
infixr 0 _︔_
_︔_ : ∀ {x y z} → x ≈ y → y ≈ z → x ≈ z
_︔_ = trans

-- If a function (a cangruence, for instance) appropriately changes
-- the relation, it can be applied with this combinator. It is
-- useful if both sides of the equation are getting large, and you
-- want to "cancel from both sides" with something.
infixr 2 _≅⟨_⟩_
_≅⟨_⟩_ : ∀ w {x y z} → (y ≈ z → w ≈ x) → y IsRelatedTo z → w IsRelatedTo x
_ ≅⟨ congruence ⟩ relTo y~z = relTo (congruence y~z)
