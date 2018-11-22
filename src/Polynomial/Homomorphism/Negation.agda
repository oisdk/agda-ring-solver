{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Polynomial.Parameters

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomial.Homomorphism.Negation
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open Homomorphism homo
open import Polynomial.Homomorphism.Lemmas homo
open import Polynomial.Reasoning ring
open import Polynomial.NormalForm homo

open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product hiding (Σ)
import Data.Nat.Properties as ℕ-≡
import Relation.Binary.PropositionalEquality as ≡
open import Function
open import Data.List as List using (_∷_; []; foldr)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Level using (Lift; lower; lift)
open import Data.Fin as Fin using (Fin)
open import Induction.WellFounded
open import Induction.Nat

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
      neg-step = λ x {ys} zs ys≋zs →
        begin
          ⟦ ⊟-step (wf _ i≤n) x ⟧ ρs + Σ⟦ ys ⟧ (ρ , ρs) * ρ
        ≈⟨ ⊟-step-hom (wf _ i≤n) x ρs ⟨ +-cong ⟩ (≪* ys≋zs) ⟩
          - ⟦ x ⟧ ρs + - Σ⟦ zs ⟧ (ρ , ρs) * ρ
        ≈⟨ (+≫ -‿*-distribˡ _ _)  ⟨ trans ⟩ -‿+-comm _ _ ⟩
          - (⟦ x ⟧ ρs + Σ⟦ zs ⟧ (ρ , ρs) * ρ)
        ∎
  in
  begin
    ⟦ para (⊟-cons (wf _ i≤n)) xs Π↓ i≤n ⟧ ρ′
  ≈⟨ Π↓-hom (para (⊟-cons _) xs) i≤n ρ′ ⟩
    Σ⟦ para (⊟-cons _) xs ⟧ (ρ , ρs)
  ≈⟨ poly-foldR ρ ρs (⊟-cons (wf _ i≤n)) -_ -‿*-distribˡ neg-step neg-zero xs ⟩
    - Σ⟦ xs ⟧ (ρ , ρs)
  ∎

⊟-hom : ∀ {n}
      → (xs : Poly n)
      → (Ρ : Vec Carrier n)
      → ⟦ ⊟ xs ⟧ Ρ ≈ - ⟦ xs ⟧ Ρ
⊟-hom = ⊟-step-hom (<′-wellFounded _)
