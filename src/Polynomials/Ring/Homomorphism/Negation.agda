{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Ring.Homomorphism.Negation
  {r₁ r₂ r₃ r₄}
  (coeff : RawRing r₁)
  (Zero-C : Pred (RawRing.Carrier coeff) r₂)
  (zero-c? : Decidable Zero-C)
  (ring : AlmostCommutativeRing r₃ r₄)
  (morphism : coeff -Raw-AlmostCommutative⟶ ring)
  (Zero-C⟶Zero-R : ∀ x → Zero-C x → AlmostCommutativeRing._≈_ ring (_-Raw-AlmostCommutative⟶_.⟦_⟧ morphism x) (AlmostCommutativeRing.0# ring))
  where

open import Polynomials.Ring.Homomorphism.Lemmas coeff Zero-C zero-c? ring morphism Zero-C⟶Zero-R

open AlmostCommutativeRing ring hiding (zero)
open import Polynomials.Ring.Reasoning ring
open import Polynomials.Ring.Normal coeff Zero-C zero-c?
open import Polynomials.Ring.Semantics coeff Zero-C zero-c? ring morphism
open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧ᵣ)

open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product hiding (Σ)
import Data.Nat.Properties as ℕ-≡
import Relation.Binary.PropositionalEquality as ≡
open import Function
open import Data.List as List using (_∷_; [])
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Level using (Lift; lower; lift)
open import Data.Fin as Fin using (Fin)

open import Induction.WellFounded
open import Induction.Nat

mutual

  ⊟-hom : ∀ {n}
        → (xs : Poly n)
        → (Ρ : Vec Carrier n)
        → ⟦ ⊟ xs ⟧ Ρ ≈ - ⟦ xs ⟧ Ρ
  ⊟-hom = ⊟-step-hom (<′-wellFounded _)

  ⊟-step-hom : ∀ {n} (a : Acc ℕ._<′_ n) → (xs : Poly n) → ⟦ ⊟-step a xs ⟧ ≋ -_ ∘ ⟦ xs ⟧
  ⊟-step-hom a (Κ x  Π i≤n) Ρ = -‿homo x
  ⊟-step-hom (acc wf) (Σ xs Π i≤n) Ρ =
    begin
      ⟦ List.foldr (⊟-cons (wf _ i≤n)) [] xs Π↓ i≤n ⟧ Ρ
    ≈⟨ Π↓-hom (List.foldr (⊟-cons _) [] xs) i≤n Ρ ⟩
      Σ⟦ List.foldr (⊟-cons _) [] xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ foldr-prop  (λ ys zs → Σ⟦ ys ⟧ ≋ -_ ∘ Σ⟦ zs ⟧) neg-step (λ _ → neg-zero) xs (drop-1 i≤n Ρ) ⟩
      - Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ∎
    where
    neg-step = λ x′ {ys} {zs} ys≋zs Ρ′ →
      let x ≠0 Δ i = x′
          (ρ , Ρ″) = Ρ′
      in
      begin
        Σ⟦ ⊟-step (wf _ i≤n) x ^ i ∷↓ ys ⟧ Ρ′
      ≈⟨ ∷↓-hom (⊟-step (wf _ i≤n) x) i _ ρ Ρ″ ⟩
        (⟦ ⊟-step (wf _ i≤n) x ⟧ Ρ″ + Σ⟦ ys ⟧ (ρ , Ρ″) * ρ) * ρ ^ i
      ≈⟨ ≪* (⊟-step-hom (wf _ i≤n) x Ρ″ ⟨ +-cong ⟩ (≪* ys≋zs Ρ′)) ⟩
        (- ⟦ x ⟧ Ρ″ + - Σ⟦ zs ⟧ Ρ′ * ρ) * ρ ^ i
      ≈⟨ ≪* ((+≫ -‿*-distribˡ _ _) ⟨ trans ⟩ -‿+-comm _ _ ) ⟩
        - (⟦ x ⟧ Ρ″ + Σ⟦ zs ⟧ Ρ′ * ρ) * ρ ^ i
      ≈⟨  -‿*-distribˡ  _ _  ⟩
        - ((⟦ x ⟧ Ρ″ + Σ⟦ zs ⟧ Ρ′ * ρ) * ρ ^ i)
      ∎

  neg-zero : 0# ≈ - 0#
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
