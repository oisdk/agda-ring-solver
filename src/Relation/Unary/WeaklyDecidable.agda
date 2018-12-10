module Relation.Unary.WeaklyDecidable where

open import Relation.Nullary
open import Relation.Unary
open import Data.Maybe

WeaklyDecidable : ∀ {a ℓ} {A : Set a} → Pred A ℓ → Set _
WeaklyDecidable P = ∀ x → Maybe (P x)

dec⟶weaklyDec : ∀ {a ℓ} {A : Set a} {P : Pred A ℓ} → Decidable P → WeaklyDecidable P
dec⟶weaklyDec dec x with dec x
... | yes p = just p
... | no ¬p = nothing
