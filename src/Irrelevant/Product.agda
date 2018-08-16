{-# OPTIONS --without-K #-}

module Polynomials.Irrelevant.Product where

open import Level
open import Function

record Σ~ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,~_
  field
    fst~ : A
    .snd~ : B fst~
open Σ~ public

_×~_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A ×~ B = Σ~ A (λ _ → B)

infix 2 Σ~-syntax
Σ~-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
Σ~-syntax = Σ~

syntax Σ~-syntax A (λ x → B) = Σ~[ x ∈ A ] B

∃~ : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃~ = Σ~ _

∃~-syntax : ∀ {a b} {A : Set a} → (A → Set b) → Set (a ⊔ b)
∃~-syntax = ∃~

syntax ∃~-syntax (λ x → B) = ∃~[ x ] B
