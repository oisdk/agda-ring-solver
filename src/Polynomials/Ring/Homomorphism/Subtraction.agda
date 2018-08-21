{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Ring.Homomorphism.Subtraction
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
open import Data.Product.Irrelevant
open import Level using (Lift; lower; lift)
open import Data.Fin as Fin using (Fin)

-- mutual
--   ⊟-hom : ∀ {n}
--         → (xs : Poly n)
--         → (Ρ : Vec Carrier n)
--         → ⟦ ⊟ xs ⟧ Ρ ≈ - ⟦ xs ⟧ Ρ
--   ⊟-hom {ℕ.zero} xs [] = -‿homo _
--   ⊟-hom {suc _} xs (ρ ∷ Ρ) = ⊟-coeffs-hom xs ρ Ρ

--   ⊟-coeffs-hom : ∀ {n}
--               → (xs : Coeffs n)
--               → (ρ : Carrier)
--               → (Ρ : Vec Carrier n)
--               → ⟦ ⊟ xs ⟧ (ρ ∷ Ρ) ≈ - ⟦ xs ⟧ (ρ ∷ Ρ)
--   ⊟-coeffs-hom [] ρ Ρ =
--     begin
--       ⟦ ⊟ [] ⟧ (ρ ∷ Ρ)
--     ≡⟨⟩
--       0#
--     ≈⟨ sym (zeroʳ _) ⟩
--       - 0# * 0#
--     ≈⟨ -‿*-distribˡ 0# 0# ⟩
--       - (0# * 0#)
--     ≈⟨ -‿cong (zeroˡ 0#) ⟩
--       - 0#
--     ≡⟨⟩
--       - ⟦ [] ⟧ (ρ ∷ Ρ)
--     ∎
--   ⊟-coeffs-hom  ((x ,~ x≠0 , i) ∷ xs) ρ Ρ =
--     begin
--       ⟦ ⊟ ((x ,~ x≠0 , i) ∷ xs) ⟧ (ρ ∷ Ρ)
--     ≡⟨⟩
--       ⟦ (⊟ x , i) ∷↓ ⊟ xs ⟧ (ρ ∷ Ρ)
--     ≈⟨ ∷↓-hom (⊟ x) i (⊟ xs) ρ Ρ ⟩
--       (⟦ ⊟ x ⟧ Ρ + ⟦ ⊟ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
--     ≈⟨ ≪* (⊟-hom x Ρ ⟨ +-cong ⟩ (≪* ⊟-coeffs-hom xs ρ Ρ)) ⟩
--       (- ⟦ x ⟧ Ρ + - ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
--     ≈⟨ ≪* +≫ -‿*-distribˡ _ ρ ⟩
--       (- ⟦ x ⟧ Ρ + - (⟦ xs ⟧ (ρ ∷ Ρ) * ρ)) * ρ ^ i
--     ≈⟨ ≪* -‿+-comm _ _ ⟩
--       - (⟦ x ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
--     ≈⟨ -‿*-distribˡ _ _ ⟩
--       - ⟦ (x ,~ x≠0 , i) ∷ xs ⟧ (ρ ∷ Ρ)
--     ∎
