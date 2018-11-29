module Data.Pair.NonDependent where

open import Level using (_⊔_)

infixr 2 _×_
infixr 4 _,_
record _×_ {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open _×_ public

map₁ : ∀ {a₁ a₂ b} {A₁ : Set a₁} {A₂ : Set a₂} {B : Set b}
     → (A₁ → A₂)
     → A₁ × B
     → A₂ × B
map₁ f (x , y) = f x , y

map₂ : ∀ {a b₁ b₂} {A : Set a} {B₁ : Set b₁} {B₂ : Set b₂}
     → (B₁ → B₂)
     → A × B₁
     → A × B₂
map₂ f (x , y) = x , f y

curry : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
      → (A × B → C)
      → A → B → C
curry f x y = f (x , y)

uncurry : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c}
        → (A → B → C)
        → A × B → C
uncurry f (x , y) = f x y
