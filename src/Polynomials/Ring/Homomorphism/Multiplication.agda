{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Ring.Homomorphism.Multiplication
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

mutual
  ⊠-hom : ∀ {n}
        → (xs : Poly n)
        → (ys : Poly n)
        → (Ρ : Vec Carrier n)
        → ⟦ xs ⊠ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ * ⟦ ys ⟧ Ρ
  ⊠-hom (xs Π i≤n) (ys Π j≤n) = {!!}
  -- ⊠-hom {suc n} xs ys (ρ ∷ Ρ) = ⊠-coeffs-hom xs ys ρ Ρ

  -- ⊠-step-hom : ∀ {n}
  --            → (y : Poly n)
  --            → (ys : Coeffs n)
  --            → (xs : Coeffs n)
  --            → (ρ : Carrier)
  --            → (Ρ : Vec Carrier n)
  --            → ⟦ List.foldr (⊠-step y ys) [] xs ⟧ (ρ ∷ Ρ)
  --            ≈ ⟦ xs ⟧ (ρ ∷ Ρ) * (⟦ y ⟧ Ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
  -- ⊠-step-hom y ys [] ρ Ρ = sym (zeroˡ _)
  -- ⊠-step-hom y ys ((x ,~ x≠0 , i) ∷ xs) ρ Ρ =
  --   let y′  = ⟦ y ⟧ Ρ
  --       x′  = ⟦ x ⟧ Ρ
  --       ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
  --       xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
  --       xs″ = List.foldr (⊠-step y ys) [] xs
  --   in
  --   begin
  --     ⟦ (x ⊠ y , i) ∷↓ (x ⋊ ys ⊞ xs″) ⟧ (ρ ∷ Ρ)
  --   ≈⟨  ∷↓-hom _ i _ ρ Ρ ⟩
  --     (⟦ x ⊠ y ⟧ Ρ + ⟦ x ⋊ ys ⊞ xs″ ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
  --   ≈⟨ ≪* begin
  --           ⟦ x ⊠ y ⟧ Ρ + ⟦ x ⋊ ys ⊞ xs″ ⟧ (ρ ∷ Ρ) * ρ
  --         ≈⟨ ⊠-hom x y Ρ ⟨ +-cong ⟩ (≪* ⊞-hom (x ⋊ ys) _ (ρ ∷ Ρ)) ⟩
  --           x′ * y′ + (⟦ x ⋊ ys ⟧ (ρ ∷ Ρ) + ⟦ xs″ ⟧ (ρ ∷ Ρ)) * ρ
  --         ≈⟨ +≫ ≪* (⋊-hom x ys ρ Ρ ⟨ +-cong ⟩ ⊠-step-hom y ys xs ρ Ρ) ⟩
  --           x′ * y′ + (x′ * ys′ + xs′ * (y′ + ys′ * ρ)) * ρ
  --         ≈⟨ +≫ distribʳ ρ _ _ ⟩
  --           x′ * y′ + (x′ * ys′ * ρ + xs′ * (y′ + ys′ * ρ) * ρ)
  --         ≈⟨ sym (+-assoc _ _ _) ⟩
  --           (x′ * y′ + x′ * ys′ * ρ) + xs′ * (y′ + ys′ * ρ) * ρ
  --         ≈⟨ (+≫ *-assoc _ _ _ ︔ sym (distribˡ _ _ _)) ⟨ +-cong ⟩
  --            (*-assoc _ _ _ ︔ *≫ *-comm _ _ ︔ sym (*-assoc _ _ _)) ⟩
  --           x′ * (y′ + ys′ * ρ) + xs′ * ρ * (y′ + ys′ * ρ)
  --         ≈⟨ sym (distribʳ _ _ _) ⟩
  --           (x′ + xs′ * ρ) * (y′ + ys′ * ρ)
  --         ∎
  --    ⟩
  --     (x′ + xs′ * ρ) * (y′ + ys′ * ρ) * ρ ^ i
  --   ≈⟨ *-assoc _ _ _ ︔ *≫ *-comm _ _ ︔ sym (*-assoc _ _ _) ⟩
  --     (x′ + xs′ * ρ) * ρ ^ i * (y′ + ys′ * ρ)
  --   ∎

  -- ⊠-coeffs-hom : ∀ {n}
  --              → (xs : Coeffs n)
  --              → (ys : Coeffs n)
  --              → (ρ : Carrier)
  --              → (Ρ : Vec Carrier n)
  --              → ⟦ ⊠-coeffs xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ ys ⟧ (ρ ∷ Ρ)
  -- ⊠-coeffs-hom xs [] ρ Ρ = sym (zeroʳ _)
  -- ⊠-coeffs-hom xs ((y ,~ y≠0 , j) ∷ ys) ρ Ρ =
  --   let xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
  --       y′  = ⟦ y ⟧ Ρ
  --       ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
  --   in
  --   begin
  --     ⟦ List.foldr (⊠-step y ys) [] xs ⍓ j ⟧ (ρ ∷ Ρ)
  --   ≈⟨ sym (pow-hom j (List.foldr (⊠-step y ys) [] xs) ρ Ρ) ⟩
  --     ⟦ List.foldr (⊠-step y ys) [] xs ⟧ (ρ ∷ Ρ) * ρ ^ j
  --   ≈⟨ ≪* ⊠-step-hom y ys xs ρ Ρ ⟩
  --     xs′ * (y′ + ys′ * ρ) * ρ ^ j
  --   ≈⟨ *-assoc _ _ _ ⟩
  --     xs′ * ((y′ + ys′ * ρ) * ρ ^ j)
  --   ≡⟨⟩
  --     xs′ * ⟦ (y ,~ y≠0 , j) ∷ ys ⟧ (ρ ∷ Ρ)
  --   ∎

