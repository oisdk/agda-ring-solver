{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Ring.Homomorphism.Addition
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
--   ⊞-hom : ∀ {n}
--         → (xs : Poly n)
--         → (ys : Poly n)
--         → (Ρ : Vec Carrier n)
--         → ⟦ xs ⊞ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ + ⟦ ys ⟧ Ρ
--   ⊞-hom {ℕ.zero} xs ys [] = +-homo _ _
--   ⊞-hom {suc n} xs ys (ρ ∷ Ρ) = ⊞-coeffs-hom xs ys ρ Ρ

--   ⊞-coeffs-hom : ∀ {n}
--               → (xs : Coeffs n)
--               → (ys : Coeffs n)
--               → (ρ : Carrier)
--               → (Ρ : Vec Carrier n)
--               → ⟦ ⊞-coeffs xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ xs ⟧ (ρ ∷ Ρ) + ⟦ ys ⟧ (ρ ∷ Ρ)
--   ⊞-coeffs-hom [] ys ρ Ρ = sym (+-identityˡ (⟦ ys ⟧ (ρ ∷ Ρ)))
--   ⊞-coeffs-hom ((x , i) ∷ xs) = ⊞-ne-r-hom i x xs

--   ⊞-ne-hom : ∀ {n i j}
--            → (c : ℕ.Ordering i j)
--            → (x : Coeff n)
--            → (xs : Coeffs n)
--            → (y : Coeff n)
--            → (ys : Coeffs n)
--            → (ρ : Carrier)
--            → (Ρ : Vec Carrier n)
--            → ⟦ ⊞-ne c x xs y ys ⟧ (ρ ∷ Ρ)
--            ≈ ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
--   ⊞-ne-hom (ℕ.equal i) x xs y ys ρ Ρ =
--     let x′  = ⟦ proj₁~ x ⟧ Ρ
--         y′  = ⟦ proj₁~ y ⟧ Ρ
--         xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
--         ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
--     in
--     begin
--       ⟦ (proj₁~ x ⊞ proj₁~ y , i) ∷↓ xs ⊞ ys ⟧ (ρ ∷ Ρ)
--     ≈⟨ ∷↓-hom _ i (xs ⊞ ys) ρ Ρ ⟩
--       (⟦ proj₁~ x ⊞ proj₁~ y ⟧ Ρ + ⟦ xs ⊞ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
--     ≈⟨ ≪* begin
--             ⟦ proj₁~ x ⊞ proj₁~ y ⟧ Ρ + ⟦ xs ⊞ ys ⟧ (ρ ∷ Ρ) * ρ
--           ≈⟨ ⊞-hom (proj₁~ x) (proj₁~ y) Ρ ⟨ +-cong ⟩ (≪* ⊞-coeffs-hom xs ys ρ Ρ) ⟩
--             (x′ + y′) + (xs′ + ys′) * ρ
--           ≈⟨ +≫ distribʳ ρ _ _ ⟩
--             (x′ + y′) + (xs′ * ρ + ys′ * ρ)
--           ≈⟨ +-assoc x′ y′ _ ⟩
--             x′ + (y′ + (xs′ * ρ + ys′ * ρ))
--           ≈⟨ +≫ sym ( +-assoc y′ _ _ ) ⟩
--             x′ + ((y′ + xs′ * ρ) + ys′ * ρ)
--           ≈⟨ +≫ ≪+ +-comm y′ _ ⟩
--             x′ + ((xs′ * ρ + y′) + ys′ * ρ)
--           ≈⟨ +≫ +-assoc _ y′ _ ⟩
--             x′ + (xs′ * ρ + (y′ + ys′ * ρ))
--           ≈⟨ sym (+-assoc x′ _ _) ⟩
--             (x′ + xs′ * ρ) + (y′ + ys′ * ρ)
--           ∎ ⟩
--       ((x′ + xs′ * ρ) + (y′ + ys′ * ρ)) * ρ ^ i
--     ≈⟨ distribʳ (ρ ^ i) _ _ ⟩
--       (x′ + xs′ * ρ) * ρ ^ i + (y′ + ys′ * ρ) * ρ ^ i
--     ∎
--   ⊞-ne-hom (ℕ.less i k) x xs y ys ρ Ρ = ⊞-ne-r-step-hom i k y ys x xs ρ Ρ ︔ +-comm _ _
--   ⊞-ne-hom (ℕ.greater j k) = ⊞-ne-r-step-hom j k

--   ⊞-ne-r-step-hom : ∀ {n} j k
--                   → (x : Coeff n)
--                   → (xs : Coeffs n)
--                   → (y : Coeff n)
--                   → (ys : Coeffs n)
--                   → (ρ : Carrier)
--                   → (Ρ : Vec Carrier n)
--                   → ⟦ (y , j) ∷ ⊞-ne-r k x xs ys ⟧ (ρ ∷ Ρ)
--                   ≈ ⟦ (x , suc (j ℕ.+ k)) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
--   ⊞-ne-r-step-hom j k x xs y ys ρ Ρ =
--     let x′  = ⟦ proj₁~ x ⟧ Ρ
--         y′  = ⟦ proj₁~ y ⟧ Ρ
--         xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
--         ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
--     in
--     begin
--       (y′ + ⟦ ⊞-ne-r k x xs ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j
--     ≈⟨ ≪* +≫ ≪* ⊞-ne-r-hom k x xs ys ρ Ρ ⟩
--       (y′ + ((x′ + xs′ * ρ) * ρ ^ k + ys′) * ρ) * ρ ^ j
--     ≈⟨ ≪* +≫ distribʳ ρ _ _ ⟩
--       (y′ + ((x′ + xs′ * ρ) * ρ ^ k * ρ + ys′ * ρ)) * ρ ^ j
--     ≈⟨ ≪* (sym (+-assoc _ _ _) ︔ ≪+ +-comm _ _ ︔ +-assoc _ _ _) ⟩
--       ((x′ + xs′ * ρ) * ρ ^ k * ρ + (y′ + ys′ * ρ)) * ρ ^ j
--     ≈⟨ distribʳ (ρ ^ j) _ _ ⟩
--       (x′ + xs′ * ρ) * ρ ^ k * ρ * ρ ^ j + (y′ + ys′ * ρ) * ρ ^ j
--     ≈⟨ ≪+ begin
--              (((x′ + xs′ * ρ) * ρ ^ k) * ρ) * ρ ^ j
--            ≈⟨ *-assoc _ ρ (ρ ^ j) ⟩
--              ((x′ + xs′ * ρ) * ρ ^ k) * (ρ * ρ ^ j)
--            ≈⟨ *-assoc _ _ _ ⟩
--              (x′ + xs′ * ρ) * (ρ ^ k * (ρ * ρ ^ j))
--            ≈⟨ *≫ begin
--                     ρ ^ k * (ρ * ρ ^ j)
--                   ≈⟨ pow-add ρ k _ ⟩
--                     ρ ^ (k ℕ.+ suc j)
--                   ≡⟨ ≡.cong (ρ ^_) (ℕ-≡.+-comm k (suc j)) ⟩
--                     ρ ^ suc (j ℕ.+ k)
--                   ∎ ⟩
--              (x′ + xs′ * ρ) * ρ ^ suc (j ℕ.+ k)
--            ∎ ⟩
--       (x′ + xs′ * ρ) * ρ ^ suc (j ℕ.+ k) + (y′ + ys′ * ρ) * ρ ^ j
--     ≡⟨⟩
--       ⟦ (x , suc (j ℕ.+ k)) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
--     ∎

--   ⊞-ne-r-hom : ∀ {n} i
--              → (x : Coeff n)
--              → (xs : Coeffs n)
--              → (ys : Coeffs n)
--              → (ρ : Carrier)
--              → (Ρ : Vec Carrier n)
--              → ⟦ ⊞-ne-r i x xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ ys ⟧ (ρ ∷ Ρ)
--   ⊞-ne-r-hom i x xs [] ρ Ρ = sym (+-identityʳ _)
--   ⊞-ne-r-hom i x xs ((y , j) ∷ ys) = ⊞-ne-hom (ℕ.compare i j) x xs y ys
