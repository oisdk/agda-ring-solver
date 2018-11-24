{-# OPTIONS --without-K --safe #-}

-- This module provides the basic expression type for polynomials.

module Polynomial.Expr where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

infixl 6 _⊕_
infixl 7 _⊗_
data Expr  {ℓ} (A : Set ℓ) (n : ℕ) : Set ℓ where
  Κ   : A → Expr A n
  Ι   : Fin n → Expr A n
  _⊕_ : Expr A n → Expr A n → Expr A n
  _⊗_ : Expr A n → Expr A n → Expr A n
  ⊝_  : Expr A n → Expr A n

open import Polynomial.Parameters

module Eval {r₁ r₂ r₃ r₄} (homo : Homomorphism r₁ r₂ r₃ r₄) where
  open Homomorphism homo

  open import Data.Vec as Vec using (Vec)

  ⟦_⟧ : ∀ {n} → Expr Raw.Carrier n → Vec Carrier n → Carrier
  ⟦ Κ x ⟧ ρ = ⟦ x ⟧ᵣ
  ⟦ Ι x ⟧ ρ = Vec.lookup x ρ
  ⟦ x ⊕ y ⟧ ρ = ⟦ x ⟧ ρ + ⟦ y ⟧ ρ
  ⟦ x ⊗ y ⟧ ρ = ⟦ x ⟧ ρ * ⟦ y ⟧ ρ
  ⟦ ⊝ x ⟧ ρ = - ⟦ x ⟧ ρ
