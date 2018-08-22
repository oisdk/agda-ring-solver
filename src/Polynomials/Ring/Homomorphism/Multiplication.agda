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
open import Polynomials.Ring.Homomorphism.Addition coeff Zero-C zero-c? ring morphism Zero-C⟶Zero-R
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

mutual
  ⊠-hom : ∀ {n}
        → (xs : Poly n)
        → (ys : Poly n)
        → (Ρ : Vec Carrier n)
        → ⟦ xs ⊠ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ * ⟦ ys ⟧ Ρ
  ⊠-hom (xs Π i≤n) (ys Π j≤n) = ⊠-match-hom (i≤n ∺ j≤n) xs ys

  ⊠-match-hom : ∀ {i j n}
              → {i≤n : i ≤ n}
              → {j≤n : j ≤ n}
              → (ord : Ordering i≤n j≤n)
              → (xs : FlatPoly i)
              → (ys : FlatPoly j)
              → (Ρ : Vec Carrier n)
              → ⟦ ⊠-match ord xs ys ⟧ Ρ ≈ ⟦ xs Π i≤n ⟧ Ρ * ⟦ ys Π j≤n ⟧ Ρ
  ⊠-match-hom (i≤j-1 < j≤n) xs (Σ ys) Ρ =
    let (ρ , Ρ′) = drop-1 j≤n Ρ
    in
    begin
      ⟦ ⊠-inj i≤j-1 xs ys Π↓ j≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊠-inj i≤j-1 xs ys) j≤n Ρ ⟩
      Σ⟦ ⊠-inj i≤j-1 xs ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ⊠-inj-hom i≤j-1 xs ys ρ Ρ′ ⟩
      ⟦ xs Π i≤j-1 ⟧ (proj₂ (drop-1 j≤n Ρ)) * Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ≪* ⋈-hom i≤j-1 j≤n xs Ρ ⟩
      ⟦ xs Π (≤-s i≤j-1 ⋈ j≤n) ⟧ Ρ * Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ∎
  ⊠-match-hom (i≤n > j≤i-1) (Σ xs) ys Ρ =
    let (ρ , Ρ′) = drop-1 i≤n Ρ
    in
    begin
      ⟦ ⊠-inj j≤i-1 ys xs Π↓ i≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊠-inj j≤i-1 ys xs) i≤n Ρ ⟩
      Σ⟦ ⊠-inj j≤i-1 ys xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ⊠-inj-hom j≤i-1 ys xs ρ Ρ′ ⟩
      ⟦ ys Π j≤i-1 ⟧ (proj₂ (drop-1 i≤n Ρ)) * Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ≪* ⋈-hom j≤i-1 i≤n ys Ρ ⟩
      ⟦ ys Π (≤-s j≤i-1 ⋈ i≤n) ⟧ Ρ * Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ *-comm _ _ ⟩
      Σ⟦ xs ⟧ (drop-1 i≤n Ρ) * ⟦ ys Π (≤-s j≤i-1 ⋈ i≤n) ⟧ Ρ
    ∎
  ⊠-match-hom (eq ij≤n) (Κ x) (Κ y) Ρ = *-homo x y
  ⊠-match-hom (eq ij≤n) (Σ xs) (Σ ys) Ρ =
    begin
      ⟦ ⊠-coeffs xs ys Π↓ ij≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊠-coeffs xs ys) ij≤n Ρ ⟩
      Σ⟦ ⊠-coeffs xs ys ⟧ (drop-1 ij≤n Ρ)
    ≈⟨ ⊠-coeffs-hom xs ys (drop-1 ij≤n Ρ) ⟩
      Σ⟦ xs ⟧ (drop-1 ij≤n Ρ) * Σ⟦ ys ⟧ (drop-1 ij≤n Ρ)
    ∎
  ⊠-step-hom : ∀ {n}
             → (y : Poly n)
             → (ys : Coeffs n)
             → (xs : Coeffs n)
             → (ρ : Carrier)
             → (Ρ : Vec Carrier n)
             → Σ⟦ ⊠-step y ys xs ⟧ (ρ , Ρ)
             ≈ Σ⟦ xs ⟧ (ρ , Ρ) * (⟦ y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ)
  ⊠-step-hom y ys [] ρ Ρ = sym (zeroˡ _)
  ⊠-step-hom y ys ((x Π j≤n ≠0 Δ i) ∷ xs) ρ Ρ =
    let y′  = ⟦ y ⟧ Ρ
        x′  = ⟦ x Π j≤n ⟧ Ρ
        ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
        xs′ = Σ⟦ xs ⟧ (ρ , Ρ)
        xs″ = ⊠-step y ys xs
    in
    begin
      Σ⟦ (x Π j≤n) ⊠ y ^ i ∷↓ ⊞-coeffs (⊠-inj j≤n x ys) xs″ ⟧ (ρ , Ρ)
    ≈⟨  ∷↓-hom ((x Π j≤n) ⊠ y) i _ ρ Ρ ⟩
      (⟦ (x Π j≤n) ⊠ y ⟧ Ρ + Σ⟦ ⊞-coeffs (⊠-inj j≤n x ys) xs″ ⟧ (ρ , Ρ) * ρ) * ρ ^ i
    ≈⟨ ≪* begin
            ⟦ (x Π j≤n) ⊠ y ⟧ Ρ + Σ⟦ ⊞-coeffs (⊠-inj j≤n x ys) xs″ ⟧ (ρ , Ρ) * ρ
          ≈⟨ ⊠-hom (x Π j≤n) y Ρ ⟨ +-cong ⟩ (≪* ⊞-coeffs-hom (⊠-inj j≤n x ys) _ (ρ , Ρ)) ⟩
            x′ * y′ + (Σ⟦ ⊠-inj j≤n x ys ⟧ (ρ , Ρ) + Σ⟦ xs″ ⟧ (ρ , Ρ)) * ρ
          ≈⟨ +≫ ≪* (⊠-inj-hom j≤n x ys ρ Ρ ⟨ +-cong ⟩ ⊠-step-hom y ys xs ρ Ρ) ⟩
            x′ * y′ + (x′ * ys′ + xs′ * (y′ + ys′ * ρ)) * ρ
          ≈⟨ +≫ distribʳ ρ _ _ ⟩
            x′ * y′ + (x′ * ys′ * ρ + xs′ * (y′ + ys′ * ρ) * ρ)
          ≈⟨ sym (+-assoc _ _ _) ⟩
            (x′ * y′ + x′ * ys′ * ρ) + xs′ * (y′ + ys′ * ρ) * ρ
          ≈⟨ (+≫ *-assoc _ _ _ ︔ sym (distribˡ _ _ _)) ⟨ +-cong ⟩
             (*-assoc _ _ _ ︔ *≫ *-comm _ _ ︔ sym (*-assoc _ _ _)) ⟩
            x′ * (y′ + ys′ * ρ) + xs′ * ρ * (y′ + ys′ * ρ)
          ≈⟨ sym (distribʳ _ _ _) ⟩
            (x′ + xs′ * ρ) * (y′ + ys′ * ρ)
          ∎
     ⟩
      (x′ + xs′ * ρ) * (y′ + ys′ * ρ) * ρ ^ i
    ≈⟨ *-assoc _ _ _ ︔ *≫ *-comm _ _ ︔ sym (*-assoc _ _ _) ⟩
      (x′ + xs′ * ρ) * ρ ^ i * (y′ + ys′ * ρ)
    ∎

  ⊠-coeffs-hom : ∀ {n}
               → (xs : Coeffs n)
               → (ys : Coeffs n)
               → (Ρ : Carrier × Vec Carrier n)
               → Σ⟦ ⊠-coeffs xs ys ⟧ Ρ ≈ Σ⟦ xs ⟧ Ρ * Σ⟦ ys ⟧ Ρ
  ⊠-coeffs-hom xs [] Ρ = sym (zeroʳ _)
  ⊠-coeffs-hom xs (y ≠0 Δ j ∷ ys) (ρ , Ρ) =
    let xs′ = Σ⟦ xs ⟧ (ρ , Ρ)
        y′  = ⟦ y ⟧ Ρ
        ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      Σ⟦ ⊠-step y ys xs ⍓ j ⟧ (ρ , Ρ)
    ≈⟨ sym (pow-hom j (⊠-step y ys xs) ρ Ρ) ⟩
      Σ⟦ ⊠-step y ys xs ⟧ (ρ , Ρ) * ρ ^ j
    ≈⟨ ≪* ⊠-step-hom y ys xs ρ Ρ ⟩
      xs′ * (y′ + ys′ * ρ) * ρ ^ j
    ≈⟨ *-assoc _ _ _ ⟩
      xs′ * ((y′ + ys′ * ρ) * ρ ^ j)
    ∎

  ⊠-inj-hom : ∀ {i k}
            → (i≤k : i ≤ k)
            → (x : FlatPoly i)
            → (ys : Coeffs k)
            → (ρ : Carrier)
            → (Ρ : Vec Carrier k)
            → Σ⟦ ⊠-inj i≤k x ys ⟧ (ρ , Ρ) ≈ ⟦ x Π i≤k ⟧ Ρ * Σ⟦ ys ⟧ (ρ , Ρ)
  ⊠-inj-hom i≤k x [] ρ Ρ = sym (zeroʳ _)
  ⊠-inj-hom i≤k x (y Π j≤k ≠0 Δ j ∷ ys) ρ Ρ =
    let x′  = ⟦ x Π i≤k ⟧ Ρ
        y′  = ⟦ y Π j≤k ⟧ Ρ
        ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      Σ⟦ ⊠-match (i≤k ∺ j≤k) x y ^ j ∷↓ ⊠-inj i≤k x ys ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom (⊠-match (i≤k ∺ j≤k) x y) j (⊠-inj i≤k x ys) ρ Ρ ⟩
      (⟦ ⊠-match (i≤k ∺ j≤k) x y ⟧ Ρ + Σ⟦ ⊠-inj i≤k x ys ⟧ (ρ , Ρ) * ρ) * ρ ^ j
    ≈⟨ ≪* (⊠-match-hom (i≤k ∺ j≤k) x y Ρ ⟨ +-cong ⟩ (≪* ⊠-inj-hom i≤k x ys ρ Ρ ︔ *-assoc _ _ _))⟩
      (x′ * y′ + x′ * (ys′ * ρ)) * ρ ^ j
    ≈⟨ ≪* sym (distribˡ x′ _ _ ) ⟩
      x′ * (y′ + ys′ * ρ) * ρ ^ j
    ≈⟨ *-assoc _ _ _ ⟩
      x′ * ((y′ + ys′ * ρ) * ρ ^ j)
    ∎
