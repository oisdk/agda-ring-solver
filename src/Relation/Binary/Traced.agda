open import Relation.Binary
open import Data.String
open import Level using (_⊔_)

module Relation.Binary.Traced {a} (A : Set a) where

infix 4 _≡⋯≡_
infixr 5 _≡⟨_⟩_
data _≡⋯≡_ : A → A → Set a where
  [refl] : ∀ {x} →  x ≡⋯≡ x
  _≡⟨_⟩_ : ∀ {x} y {z} → String → y ≡⋯≡ z → x ≡⋯≡ z
  cong₁ : ∀ {x y z} {f : A → A}
        → String
        → x ≡⋯≡ y
        → f y ≡⋯≡ z
        → f x ≡⋯≡ z
  cong₂ : ∀ {x₁ x₂ y₁ y₂ z} {f : A → A → A}
        → String
        → x₁ ≡⋯≡ x₂
        → y₁ ≡⋯≡ y₂
        → f x₂ y₂ ≡⋯≡ z
        → f x₁ y₁ ≡⋯≡ z

trans-≡⋯≡ : ∀ {x y z} → x ≡⋯≡ y → y ≡⋯≡ z → x ≡⋯≡ z
trans-≡⋯≡ [refl] ys = ys
trans-≡⋯≡ (y ≡⟨ x₁ ⟩ xs) ys = y ≡⟨ x₁ ⟩ (trans-≡⋯≡ xs ys)
trans-≡⋯≡ (cong₁ e x≡y fy≡z) ys = cong₁ e x≡y (trans-≡⋯≡ fy≡z ys)
trans-≡⋯≡ (cong₂ e x y fxy≡z) ys = cong₂ e x y (trans-≡⋯≡ fxy≡z ys)

cong′ : ∀ {x y} → (f : A → A) → x ≡⋯≡ y → f x ≡⋯≡ f y
cong′ f xs = cong₁ "cong" xs [refl]

sym-≡⋯≡ : ∀ {x y} → x ≡⋯≡ y → y ≡⋯≡ x
sym-≡⋯≡ {x} {y} = go [refl]
  where
    go : ∀ {z} → z ≡⋯≡ x → z ≡⋯≡ y → y ≡⋯≡ x
    go xs [refl] = xs
    go xs (y ≡⟨ y? ⟩ ys) = go (_ ≡⟨ y? ⟩ xs) ys
    go xs (cong₁ e ys zs) = go (cong₁ e ys (_ ≡⟨ e ⟩ xs)) zs
    go xs (cong₂ e xp yp zp) = go (cong₂ e xp yp (_ ≡⟨ e ⟩ xs)) zp

≡⋯≡-equiv : IsEquivalence _≡⋯≡_
≡⋯≡-equiv = record
  { refl = [refl]
  ; trans = trans-≡⋯≡
  ; sym = sym-≡⋯≡
  }
