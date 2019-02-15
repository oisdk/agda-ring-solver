open import Relation.Binary

module Relation.Binary.Reasoning.Inference
  {a ℓ}
  {A : Set a}
  (_~_ : Rel A ℓ)
  (refl : Reflexive _~_)
  (trans : Transitive _~_)
  where

open import Relation.Binary.Reasoning.Base.Single _~_ refl trans

infixr 2 step-≋

step-≋ : ∀ x {y z : A} → y IsRelatedTo z → x ~ y → x IsRelatedTo z
step-≋ x y~z x~y = x ∼⟨ x~y ⟩ y~z

syntax step-≋ x y≡z x≡y = x ≋⟨ x≡y ⟩ y≡z
