{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters

module Polynomial.Homomorphism.Negation
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Pair.NonDependent          using (_,_)
open import Data.Vec              using (Vec)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat         using (<′-wellFounded)

open import Function

open Homomorphism homo
open import Polynomial.Homomorphism.Lemmas homo
open import Polynomial.Reasoning ring
open import Polynomial.NormalForm homo

⊟-step-hom : ∀ {n} (a : Acc _<′_ n) → (xs : Poly n) → ∀ ρ → ⟦ ⊟-step a xs ⟧ ρ ≈ - (⟦ xs ⟧ ρ)
⊟-step-hom a (Κ x  Π i≤n) ρ = -‿homo x
⊟-step-hom (acc wf) (Σ xs Π i≤n) ρ′ =
  let (ρ , ρs) = drop-1 i≤n ρ′
      neg-zero =
        begin
          0#
        ≈⟨ sym (zeroʳ _) ⟩
          - 0# * 0#
        ≈⟨ -‿*-distribˡ 0# 0# ⟩
          - (0# * 0#)
        ≈⟨ -‿cong (zeroˡ 0#) ⟩
          - 0#
        ∎
  in
  begin
    ⟦ poly-map (⊟-step (wf _ i≤n)) xs Π↓ i≤n ⟧ ρ′
  ≈⟨ Π↓-hom (poly-map (⊟-step _) xs) i≤n ρ′ ⟩
    Σ⟦ poly-map (⊟-step _) xs ⟧ (ρ , ρs)
  ≈⟨ poly-mapR ρ ρs (⊟-step (wf _ i≤n)) -_ -‿*-distribˡ (λ x y → sym (-‿+-comm x y)) (flip (⊟-step-hom (wf _ i≤n)) ρs) (sym neg-zero ) xs ⟩
    - Σ⟦ xs ⟧ (ρ , ρs)
  ∎

⊟-hom : ∀ {n}
      → (xs : Poly n)
      → (Ρ : Vec Carrier n)
      → ⟦ ⊟ xs ⟧ Ρ ≈ - ⟦ xs ⟧ Ρ
⊟-hom = ⊟-step-hom (<′-wellFounded _)
