open import Relation.Binary
open import Data.String
open import Level using (_⊔_)

module Relation.Binary.Traced
  {a ℓ}
  (setoid : Setoid a ℓ)
  where

open Setoid setoid renaming (trans to trans′; sym to sym′; refl to refl′)

infix 4 _≡⋯≡_
infixr 5 _≡⟨_⟩_
data _≡⋯≡_ (x : Carrier) : Carrier → Set (a ⊔ ℓ) where
  [refl] : x ≡⋯≡ x
  _≡⟨_⟩_ : ∀ {y z} → x ≈ y → String → y ≡⋯≡ z → x ≡⋯≡ z

trans-≡⋯≡ : ∀ {x y z} → x ≡⋯≡ y → y ≡⋯≡ z → x ≡⋯≡ z
trans-≡⋯≡ [refl] ys = ys
trans-≡⋯≡ (x ≡⟨ x? ⟩ xs) ys = x ≡⟨ x? ⟩ (trans-≡⋯≡ xs ys)

sym-≡⋯≡ : ∀ {x y} → x ≡⋯≡ y → y ≡⋯≡ x
sym-≡⋯≡ {x} {y} = go [refl]
  where
    go : ∀ {z} → z ≡⋯≡ x → z ≡⋯≡ y → y ≡⋯≡ x
    go xs [refl] = xs
    go xs (y ≡⟨ y? ⟩ ys) = go (sym′ y ≡⟨ y? ⟩ xs) ys

open Setoid
open IsEquivalence
≡⋯≡-setoid : Setoid a (a ⊔ ℓ)
Carrier ≡⋯≡-setoid = Carrier setoid
_≈_ ≡⋯≡-setoid = _≡⋯≡_
refl  (isEquivalence ≡⋯≡-setoid) = [refl]
trans (isEquivalence ≡⋯≡-setoid) = trans-≡⋯≡
sym   (isEquivalence ≡⋯≡-setoid) = sym-≡⋯≡
