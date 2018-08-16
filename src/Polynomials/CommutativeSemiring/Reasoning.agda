{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
open import Relation.Binary
open import Algebra.FunctionProperties

-- Some specialised tools for equaltional reasoning.
module Polynomials.CommutativeSemiring.Reasoning
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  where

open CommutativeSemiring commutativeSemiring
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Nullary
open import Relation.Binary.EqReasoning setoid public

-- -- Standard Equational reasoning combinators

-- infix  4 _IsRelatedTo_
-- data _IsRelatedTo_ (x y : Carrier) : Set ℓ where
-- -- Maybe instance?
--   relTo : x ≈ y → x IsRelatedTo y

-- infix 1 begin_
-- begin_ : ∀ {x y} → x IsRelatedTo y → x ≈ y
-- begin relTo x≈y = x≈y

-- infixr 2 _≡⟨⟩_
-- _≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
-- _ ≡⟨⟩ x∼y = x∼y

-- -- A faster combinator, according to
-- -- https://lists.chalmers.se/pipermail/agda/2016/009090.html
-- infixr 2 step-≈

-- step-≈ : ∀ x {y z} → y IsRelatedTo z → x ≈ y → x IsRelatedTo z
-- step-≈ _ (relTo y≈z) x≈y = relTo (trans x≈y y≈z)

-- syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

-- infixr 2 step-≡

-- step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡.≡ y → x IsRelatedTo z
-- step-≡ _ (relTo y≈z) x≈y = relTo (≡.subst _ (≡.sym x≈y) y≈z)

-- syntax step-≡ x y≈z x≈y = x ≡⟨ x≈y ⟩ y≈z

-- infix 3 _∎
-- _∎ : ∀ x → x IsRelatedTo x
-- _∎ _ = relTo refl

-- These are combinators for congruence, as custom setoids don't
-- automatic congruence over function application. For each
-- operator, the arriws point towards the side being "focused" on.

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
