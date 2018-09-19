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
open import Data.List as List using (List; _∷_; []; foldr)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Level using (Lift; lower; lift)
open import Data.Fin as Fin using (Fin)
open import Induction.WellFounded


mutual
  ⊠-step-hom : ∀ {n}
             → (a : ⌊ n ⌋)
             → (xs ys : Poly n)
             → ∀ ρ
             → ⟦ ⊠-step a xs ys ⟧ ρ ≈ ⟦ xs ⟧ ρ * ⟦ ys ⟧ ρ
  ⊠-step-hom a (xs Π i≤n) (ys Π j≤n) = ⊠-match-hom a (i≤n cmp j≤n) xs ys

  ⊠-match-hom : ∀ {i j n}
              → (a : ⌊ n ⌋)
              → {i≤n : i ≤ n}
              → {j≤n : j ≤ n}
              → (ord : Ordering i≤n j≤n)
              → (xs : FlatPoly i)
              → (ys : FlatPoly j)
              → (Ρ : Vec Carrier n)
              → ⟦ ⊠-match a ord xs ys ⟧ Ρ ≈ ⟦ xs Π i≤n ⟧ Ρ * ⟦ ys Π j≤n ⟧ Ρ
  ⊠-match-hom (acc wf) (i≤j-1 < j≤n) xs (Σ ys) Ρ =
    let (ρ , Ρ′) = drop-1 j≤n Ρ
    in
    begin
      ⟦ foldr (⊠-inj (wf _ j≤n) i≤j-1 xs) [] ys Π↓ j≤n ⟧ Ρ
    ≈⟨ Π↓-hom (foldr (⊠-inj (wf _ j≤n) i≤j-1 xs) [] ys) j≤n Ρ ⟩
      Σ⟦ foldr (⊠-inj (wf _ j≤n) i≤j-1 xs) [] ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ⊠-inj-hom (wf _ j≤n) i≤j-1 xs ys ρ Ρ′ ⟩
      ⟦ xs Π i≤j-1 ⟧ (proj₂ (drop-1 j≤n Ρ)) * Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ≪* ⋈-hom i≤j-1 j≤n xs Ρ ⟩
      ⟦ xs Π (≤-s i≤j-1 ⋈ j≤n) ⟧ Ρ * Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ∎
  ⊠-match-hom (acc wf) (i≤n > j≤i-1) (Σ xs) ys Ρ =
    let (ρ , Ρ′) = drop-1 i≤n Ρ
    in
    begin
      ⟦ foldr (⊠-inj (wf _ i≤n) j≤i-1 ys) [] xs Π↓ i≤n ⟧ Ρ
    ≈⟨ Π↓-hom (foldr (⊠-inj (wf _ i≤n) j≤i-1 ys) [] xs) i≤n Ρ ⟩
      Σ⟦ foldr (⊠-inj (wf _ i≤n) j≤i-1 ys) [] xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ⊠-inj-hom (wf _ i≤n) j≤i-1 ys xs ρ Ρ′ ⟩
      ⟦ ys Π j≤i-1 ⟧ (proj₂ (drop-1 i≤n Ρ)) * Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ≪* ⋈-hom j≤i-1 i≤n ys Ρ ⟩
      ⟦ ys Π (≤-s j≤i-1 ⋈ i≤n) ⟧ Ρ * Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ *-comm _ _ ⟩
      Σ⟦ xs ⟧ (drop-1 i≤n Ρ) * ⟦ ys Π (≤-s j≤i-1 ⋈ i≤n) ⟧ Ρ
    ∎
  ⊠-match-hom (acc _) (eq ij≤n) (Κ x) (Κ y) Ρ = *-homo x y
  ⊠-match-hom (acc wf) (eq ij≤n) (Σ xs) (Σ ys) Ρ =
    begin
      ⟦ ⊠-coeffs (wf _ ij≤n) xs ys Π↓ ij≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊠-coeffs (wf _ ij≤n) xs ys) ij≤n Ρ ⟩
      Σ⟦ ⊠-coeffs (wf _ ij≤n) xs ys ⟧ (drop-1 ij≤n Ρ)
    ≈⟨ ⊠-coeffs-hom (wf _ ij≤n) xs ys (drop-1 ij≤n Ρ) ⟩
      Σ⟦ xs ⟧ (drop-1 ij≤n Ρ) * Σ⟦ ys ⟧ (drop-1 ij≤n Ρ)
    ∎
  ⊠-cons-hom : ∀ {n}
             → (a : ⌊ n ⌋)
             → (y : Poly n)
             → (ys : Coeffs n)
             → (xs : Coeffs n)
             → (ρ : Carrier)
             → (Ρ : Vec Carrier n)
             → Σ⟦ foldr (⊠-cons a y ys) [] xs ⟧ (ρ , Ρ)
             ≈ Σ⟦ xs ⟧ (ρ , Ρ) * (⟦ y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ)
  ⊠-cons-hom {k} a y ys xs ρ Ρ = foldr-prop (λ ys′ zs′ → ∀ ρ Ρ → Σ⟦ ys′ ⟧(ρ , Ρ) ≈ Σ⟦ zs′ ⟧ (ρ , Ρ) * (⟦ y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ)) cons-step (λ _ _ → sym (zeroˡ _)) xs ρ Ρ
    where
    cons-step : (x : CoeffExp k)
              → {ys′ zs′ : Coeffs k}
              → (∀ ρ Ρ → Σ⟦ ys′ ⟧ (ρ , Ρ) ≈ Σ⟦ zs′ ⟧ (ρ , Ρ) * (⟦ y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ))
              → ∀ ρ Ρ
              → Σ⟦ ⊠-cons a y ys x ys′ ⟧ (ρ , Ρ) ≈ Σ⟦ x ∷ zs′ ⟧ (ρ , Ρ) * (⟦ y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ)
    cons-step (x Π j≤n ≠0 Δ i) {ys″} {zs′} ys≋zs ρ Ρ =
      let x′  = ⟦ x Π j≤n ⟧ Ρ
          xs′ = Σ⟦ zs′ ⟧ (ρ , Ρ)
          y′  = ⟦ y ⟧ Ρ
          ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
      in
      begin
        Σ⟦ ⊠-step a (x Π j≤n) y ^ i ∷↓ ⊞-coeffs (foldr (⊠-inj a j≤n x) [] ys) ys″ ⟧ (ρ , Ρ)
      ≈⟨ ∷↓-hom (⊠-step a (x Π j≤n) y) i _ ρ Ρ ⟩
        (⟦ ⊠-step a (x Π j≤n) y ⟧ Ρ + Σ⟦ ⊞-coeffs (foldr (⊠-inj a j≤n x) [] ys) ys″ ⟧ (ρ , Ρ) * ρ) * ρ ^ i
      ≈⟨ ≪* begin
              ⟦ ⊠-step a (x Π j≤n) y ⟧ Ρ + Σ⟦ ⊞-coeffs (foldr (⊠-inj a j≤n x) [] ys) ys″ ⟧ (ρ , Ρ) * ρ
            ≈⟨ ⊠-step-hom a (x Π j≤n) y Ρ ⟨ +-cong ⟩ (≪* ⊞-coeffs-hom (foldr (⊠-inj a j≤n x) [] ys) _ (ρ , Ρ)) ⟩
              x′ * y′ + (Σ⟦ foldr (⊠-inj a j≤n x) [] ys ⟧ (ρ , Ρ) + Σ⟦ ys″ ⟧ (ρ , Ρ)) * ρ
            ≈⟨ +≫ ≪* (⊠-inj-hom a j≤n x ys ρ Ρ ⟨ +-cong ⟩ ys≋zs ρ Ρ) ⟩
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
               → (a : ⌊ n ⌋)
               → (xs : Coeffs n)
               → (ys : Coeffs n)
               → (Ρ : Carrier × Vec Carrier n)
               → Σ⟦ ⊠-coeffs a xs ys ⟧ Ρ ≈ Σ⟦ xs ⟧ Ρ * Σ⟦ ys ⟧ Ρ
  ⊠-coeffs-hom _ xs [] Ρ = sym (zeroʳ _)
  ⊠-coeffs-hom a xs (y ≠0 Δ j ∷ ys) (ρ , Ρ) =
    let xs′ = Σ⟦ xs ⟧ (ρ , Ρ)
        y′  = ⟦ y ⟧ Ρ
        ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      Σ⟦ foldr (⊠-cons a y ys) [] xs ⍓ j ⟧ (ρ , Ρ)
    ≈⟨ sym (pow-hom j (foldr (⊠-cons a y ys) [] xs) ρ Ρ) ⟩
      Σ⟦ foldr (⊠-cons a y ys) [] xs ⟧ (ρ , Ρ) * ρ ^ j
    ≈⟨ ≪* ⊠-cons-hom a y ys xs ρ Ρ ⟩
      xs′ * (y′ + ys′ * ρ) * ρ ^ j
    ≈⟨ *-assoc _ _ _ ⟩
      xs′ * ((y′ + ys′ * ρ) * ρ ^ j)
    ∎

  ⊠-inj-hom : ∀ {i k}
            → (a : ⌊ k ⌋)
            → (i≤k : i ≤ k)
            → (x : FlatPoly i)
            → (ys : Coeffs k)
            → (ρ : Carrier)
            → (Ρ : Vec Carrier k)
            → Σ⟦ foldr (⊠-inj a i≤k x) [] ys ⟧ (ρ , Ρ) ≈ ⟦ x Π i≤k ⟧ Ρ * Σ⟦ ys ⟧ (ρ , Ρ)
  ⊠-inj-hom {i} {k} a i≤k x xs = foldr-prop (λ ys zs → ∀ ρ Ρ → Σ⟦ ys ⟧ (ρ , Ρ) ≈ ⟦ x Π i≤k ⟧ Ρ * Σ⟦ zs ⟧ (ρ , Ρ) ) inj-step (λ _ _ → sym (zeroʳ _)) xs
    where
    inj-step : (y : CoeffExp k)
             → {ys zs : List (CoeffExp k)}
             → (∀ ρ Ρ → Σ⟦ ys ⟧ (ρ , Ρ) ≈ ⟦ x Π i≤k ⟧ Ρ * Σ⟦ zs ⟧(ρ , Ρ))
             → ∀ ρ Ρ
             → Σ⟦ ⊠-inj a i≤k x y ys ⟧ (ρ , Ρ) ≈ ⟦ x Π i≤k ⟧ Ρ * Σ⟦ y ∷ zs ⟧ (ρ , Ρ)
    inj-step (y Π j≤k ≠0 Δ j) {ys} {zs} ys≋zs ρ Ρ =
      let x′  = ⟦ x Π i≤k ⟧ Ρ
          y′  = ⟦ y Π j≤k ⟧ Ρ
          zs′ = Σ⟦ zs ⟧ (ρ , Ρ)
      in
      begin
        Σ⟦ ⊠-match a (i≤k cmp j≤k) x y ^ j ∷↓ ys ⟧ (ρ , Ρ)
      ≈⟨ ∷↓-hom (⊠-match a (i≤k cmp j≤k) x y) j _ ρ Ρ ⟩
        (⟦ ⊠-match a (i≤k cmp j≤k) x y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ j
      ≈⟨ ≪* (⊠-match-hom a (i≤k cmp j≤k) x _ Ρ ⟨ +-cong ⟩ (≪* ys≋zs ρ Ρ ︔ *-assoc _ _ _))⟩
        (x′ * y′ + x′ * (zs′ * ρ)) * ρ ^ j
      ≈⟨ ≪* sym (distribˡ x′ _ _ ) ⟩
        x′ * (y′ + zs′ * ρ) * ρ ^ j
      ≈⟨ *-assoc _ _ _ ⟩
        x′ * ((y′ + zs′ * ρ) * ρ ^ j)
      ∎

⊠-hom : ∀ {n}
      → (xs : Poly n)
      → (ys : Poly n)
      → (Ρ : Vec Carrier n)
      → ⟦ xs ⊠ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ * ⟦ ys ⟧ Ρ
⊠-hom = ⊠-step-hom ⌊↓⌋
