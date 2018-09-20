module Relation.Binary.Lifted where

open import Function

infixl 1 _⟅_⟆_
_⟅_⟆_ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : A → Set c} {D : (x : A) → B x → C x → Set d  }
      → (f : (x : A) → B x)
      → (_*_ : {x : A} → (x′ : B x) → (y′ : C x) → D x x′ y′)
      → (g : (x : A) → C x)
      → (x : A) → D x (f x) (g x)
f ⟅ _*_ ⟆ g = λ x → f x * g x

open import Relation.Binary
open import Level using (_⊔_)

module Intensional {ℓ₁ ℓ₂} (setoid : Setoid ℓ₁ ℓ₂) where
  module Point = Setoid setoid

  infix 4 _≋_
  _≋_ : ∀ {d} {Domain : Set d} → (f g : Domain → Point.Carrier) → Set (d ⊔ ℓ₂)
  f ≋ g = ∀ x → f x Point.≈ g x

  ≋-setoid : ∀ {d} {Domain : Set d} → Setoid _ _
  ≋-setoid {_} {Domain} = record
    { Carrier = Domain → Point.Carrier
    ; _≈_ = _≋_
    ; isEquivalence = record
      { refl = λ _ → Point.refl
      ; sym  = λ eq → Point.sym ∘ eq
      ; trans = _⟅ Point.trans ⟆_
      }
    }

module Reader where
  pure : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
  pure = const

  _<*>_ : ∀ {a b c}
            {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} →
            ((x : A) (y : B x) → C x y) →
            (g : (x : A) → B x) →
            ((x : A) → C x (g x))
  f <*> g = λ x → f x (g x)

  ρ : ∀ {a} {A : Set a} → A → A
  ρ x = x

  κ : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
  κ = const
