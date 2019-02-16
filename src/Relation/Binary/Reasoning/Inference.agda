{-# OPTIONS --without-K --safe #-}

open import Relation.Binary

module Relation.Binary.Reasoning.Inference
  {a ℓ}
  (setoid : Setoid a ℓ)
  where

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

open Setoid setoid

infix  4 _IsRelatedTo_
infix  3 _∎
infixr 2 step-≈ step-≈˘ step-≡ step-≡˘
infixr 2 _≡⟨⟩_
infix  1 begin_

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data _IsRelatedTo_ (x y : Carrier) : Set ℓ where
  relTo : (x≈y : x ≈ y) → x IsRelatedTo y

begin_ : ∀ {x y} → x IsRelatedTo y → x ≈ y
begin relTo x≈y = x≈y

step-≈ : ∀ x {y z} → y IsRelatedTo z → x ≈ y → x IsRelatedTo z
step-≈ _ (relTo y≈z) x≈y = relTo (trans x≈y y≈z)

syntax step-≈ x y≈z x≈y = x ≈⟨ x≈y ⟩ y≈z

step-≈˘ : ∀ x {y z} → y IsRelatedTo z → y ≈ x → x IsRelatedTo z
step-≈˘ _ (relTo y≈z) y≈x = relTo (trans (sym y≈x) y≈z)

syntax step-≈˘ x y≈z y≈x = x ≈˘⟨ y≈x ⟩ y≈z

step-≡ : ∀ x {y z} → y IsRelatedTo z → x ≡ y → x IsRelatedTo z
step-≡ _ x≈z ≡.refl = x≈z

syntax step-≡ x y≡z x≡y = x ≡⟨ x≡y ⟩ y≡z

step-≡˘ : ∀ x {y z} → y IsRelatedTo z → y ≡ x → x IsRelatedTo z
step-≡˘ _ x≈z ≡.refl = x≈z

syntax step-≡˘ x y≡z y≡x = x ≡˘⟨ y≡x ⟩ y≡z

_≡⟨⟩_ : ∀ x {y} → x IsRelatedTo y → x IsRelatedTo y
_ ≡⟨⟩ x≈y = _ ≡⟨ ≡.refl ⟩ x≈y

_∎ : ∀ x → x IsRelatedTo x
_∎ _ = relTo refl
