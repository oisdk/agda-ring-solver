{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Polynomials.Ring.Normal.Parameters

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Ring.Homomorphism.Semantics
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Polynomials.Ring.Homomorphism.Lemmas homo
open import Polynomials.Ring.Normal homo
open Homomorphism homo
open import Polynomials.Ring.Reasoning ring

open import Data.Product hiding (Σ)
open import Function
open import Data.List as List using (_∷_; [])
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Level using (Lift; lower; lift)
open import Data.Fin as Fin using (Fin)

κ-hom : ∀ {n}
      → (x : Raw.Carrier)
      → (Ρ : Vec Carrier n)
      → ⟦ κ x ⟧ Ρ ≈ ⟦ x ⟧ᵣ
κ-hom x _ = refl

ι-hom : ∀ {n} → (i : Fin n) → (Ρ : Vec Carrier n) → ⟦ ι i ⟧ Ρ ≈ Vec.lookup i Ρ
ι-hom i Ρ′ =
  let (ρ , Ρ) = drop-1 (Fin⇒≤ i) Ρ′
  in
  begin
    ⟦ (κ Raw.1# Δ 1 ∷↓ []) Π↓ Fin⇒≤ i ⟧ Ρ′
  ≈⟨ Π↓-hom (κ Raw.1# Δ 1 ∷↓ []) (Fin⇒≤ i) Ρ′ ⟩
    Σ⟦ κ Raw.1# Δ 1 ∷↓ [] ⟧ (ρ , Ρ)
  ≈⟨ ∷↓-hom (κ Raw.1#) 1 [] ρ Ρ  ⟩
    (⟦ κ Raw.1# ⟧ Ρ + Σ⟦ [] ⟧ (ρ , Ρ) * ρ) * ρ ^ 1
  ≡⟨⟩
    (⟦ Raw.1# ⟧ᵣ + 0# * ρ) * (ρ * 1#)
  ≈⟨ 1-homo ⟨ +-cong ⟩ zeroˡ ρ ⟨ *-cong ⟩ *-identityʳ ρ ⟩
    (1# + 0#) * ρ
  ≈⟨ ≪* +-identityʳ _ ⟩
    1# * ρ
  ≈⟨ *-identityˡ ρ ⟩
    ρ
  ≡⟨ drop-1⇒lookup i Ρ′ ⟩
    Vec.lookup i Ρ′
  ∎
