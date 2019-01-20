{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters

module Polynomial.Homomorphism.Semantics
  {r₁ r₂ r₃}
  (homo : Homomorphism r₁ r₂ r₃)
  where


open import Data.Product    using (_,_)
open import Data.List       using ([])
open import Data.Vec as Vec using (Vec)
open import Data.Fin        using (Fin)

open import Function

open import Polynomial.Homomorphism.Lemmas homo
open import Polynomial.NormalForm homo
open Homomorphism homo
open import Polynomial.Reasoning ring

open import Polynomial.Exponentiation rawRing

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
    ρ * (ρ * 0# + ⟦ κ Raw.1# ⟧ Ρ)
  ≈⟨ *≫ (zeroʳ _ ⟨ +-cong ⟩ 1-homo) ⟩
    ρ * (0# + 1#)
  ≈⟨ *≫ +-identityˡ _ ⟩
    ρ * 1#
  ≈⟨ *-identityʳ ρ ⟩
    ρ
  ≡⟨ drop-1⇒lookup i Ρ′ ⟩
    Vec.lookup i Ρ′
  ∎
