{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters

module Polynomial.Homomorphism.Multiplication
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Nat as ℕ         using (ℕ; suc; zero)
open import Data.Product          using (_×_; _,_; proj₁; proj₂)
open import Data.List             using (_∷_; [])
open import Data.Vec              using (Vec)
open import Induction.WellFounded using (Acc; acc)
open import Induction.Nat         using (<′-wellFounded)

open import Function

open import Polynomial.Homomorphism.Lemmas homo
open import Polynomial.Homomorphism.Addition homo
open import Polynomial.NormalForm homo

open Homomorphism homo
open import Polynomial.Reasoning ring

mutual
  ⊠-step-hom : ∀ {n}
             → (a : Acc _<′_ n)
             → (xs ys : Poly n)
             → ∀ ρ
             → ⟦ ⊠-step a xs ys ⟧ ρ ≈ ⟦ xs ⟧ ρ * ⟦ ys ⟧ ρ
  ⊠-step-hom a (xs Π i≤n) (ys Π j≤n) = ⊠-match-hom a (inj-compare i≤n j≤n) xs ys

  ⊠-match-hom : ∀ {i j n}
              → (a : Acc _<′_ n)
              → {i≤n : i ≤′ n}
              → {j≤n : j ≤′ n}
              → (ord : InjectionOrdering i≤n j≤n)
              → (xs : FlatPoly i)
              → (ys : FlatPoly j)
              → (Ρ : Vec Carrier n)
              → ⟦ ⊠-match a ord xs ys ⟧ Ρ ≈ ⟦ xs Π i≤n ⟧ Ρ * ⟦ ys Π j≤n ⟧ Ρ
  ⊠-match-hom (acc wf) (inj-lt i≤j-1 j≤n) xs (Σ ys) Ρ =
    let (ρ , Ρ′) = drop-1 j≤n Ρ
    in
    begin
      ⟦ para (⊠-inj (wf _ j≤n) i≤j-1 xs) ys Π↓ j≤n ⟧ Ρ
    ≈⟨ Π↓-hom (para (⊠-inj (wf _ j≤n) i≤j-1 xs) ys) j≤n Ρ ⟩
      Σ⟦ para (⊠-inj (wf _ j≤n) i≤j-1 xs) ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ⊠-inj-hom (wf _ j≤n) i≤j-1 xs ys ρ Ρ′ ⟩
      ⟦ xs Π i≤j-1 ⟧ (proj₂ (drop-1 j≤n Ρ)) * Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ≪* trans-join-hom i≤j-1 j≤n xs Ρ ⟩
      ⟦ xs Π (≤′-step i≤j-1 ⟨ ≤′-trans ⟩ j≤n) ⟧ Ρ * Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ∎
  ⊠-match-hom (acc wf) (inj-gt i≤n j≤i-1) (Σ xs) ys Ρ =
    let (ρ , Ρ′) = drop-1 i≤n Ρ
    in
    begin
      ⟦ para (⊠-inj (wf _ i≤n) j≤i-1 ys) xs Π↓ i≤n ⟧ Ρ
    ≈⟨ Π↓-hom (para (⊠-inj (wf _ i≤n) j≤i-1 ys) xs) i≤n Ρ ⟩
      Σ⟦ para (⊠-inj (wf _ i≤n) j≤i-1 ys) xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ⊠-inj-hom (wf _ i≤n) j≤i-1 ys xs ρ Ρ′ ⟩
      ⟦ ys Π j≤i-1 ⟧ (proj₂ (drop-1 i≤n Ρ)) * Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ≪* trans-join-hom j≤i-1 i≤n ys Ρ ⟩
      ⟦ ys Π (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n) ⟧ Ρ * Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ *-comm _ _ ⟩
      Σ⟦ xs ⟧ (drop-1 i≤n Ρ) * ⟦ ys Π (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n) ⟧ Ρ
    ∎
  ⊠-match-hom (acc _) (inj-eq ij≤n) (Κ x) (Κ y) Ρ = *-homo x y
  ⊠-match-hom (acc wf) (inj-eq ij≤n) (Σ xs) (Σ ys) Ρ =
    begin
      ⟦ ⊠-coeffs (wf _ ij≤n) xs ys Π↓ ij≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊠-coeffs (wf _ ij≤n) xs ys) ij≤n Ρ ⟩
      Σ⟦ ⊠-coeffs (wf _ ij≤n) xs ys ⟧ (drop-1 ij≤n Ρ)
    ≈⟨ ⊠-coeffs-hom (wf _ ij≤n) xs ys (drop-1 ij≤n Ρ) ⟩
      Σ⟦ xs ⟧ (drop-1 ij≤n Ρ) * Σ⟦ ys ⟧ (drop-1 ij≤n Ρ)
    ∎
  ⊠-cons-hom : ∀ {n}
             → (a : Acc _<′_ n)
             → (y : Poly n)
             → (ys : Coeffs n)
             → (xs : Coeffs n)
             → (ρ : Carrier)
             → (Ρ : Vec Carrier n)
             → Σ⟦ para (⊠-cons a y ys) xs ⟧ (ρ , Ρ)
             ≈ Σ⟦ xs ⟧ (ρ , Ρ) * (⟦ y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ)
  ⊠-cons-hom a y ys xs ρ Ρ = poly-foldR ρ Ρ (⊠-cons a y ys) (_* (⟦ y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ)) dist step base xs
    where
    dist = λ x y → *-assoc x _ y ⟨ trans ⟩ (*≫ *-comm _ y) ⟨ trans ⟩ sym (*-assoc x y _)
    base = sym (zeroˡ _)
    step = λ { (z Π j≤n) {ys₁} zs ys≋zs →
      let x′  = ⟦ z Π j≤n ⟧ Ρ
          xs′ = Σ⟦ zs ⟧ (ρ , Ρ)
          y′  = ⟦ y ⟧ Ρ
          ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
      in
      begin
        ⟦ ⊠-step a (z Π j≤n) y ⟧ Ρ + Σ⟦ ⊞-coeffs (para (⊠-inj a j≤n z) ys) ys₁ ⟧ (ρ , Ρ) * ρ
      ≈⟨ ⊠-step-hom a (z Π j≤n) y Ρ ⟨ +-cong ⟩ (≪* ⊞-coeffs-hom (para (⊠-inj a j≤n z) ys) _ (ρ , Ρ)) ⟩
        x′ * y′ + (Σ⟦ para (⊠-inj a j≤n z) ys ⟧ (ρ , Ρ) + Σ⟦ ys₁ ⟧ (ρ , Ρ)) * ρ
      ≈⟨ +≫ ≪* (⊠-inj-hom a j≤n z ys ρ Ρ ⟨ +-cong ⟩ ys≋zs) ⟩
        x′ * y′ + (x′ * ys′ + xs′ * (y′ + ys′ * ρ)) * ρ
      ≈⟨ +≫ distribʳ ρ _ _ ⟩
        x′ * y′ + (x′ * ys′ * ρ + xs′ * (y′ + ys′ * ρ) * ρ)
      ≈⟨ sym (+-assoc _ _ _) ⟩
        (x′ * y′ + x′ * ys′ * ρ) + xs′ * (y′ + ys′ * ρ) * ρ
      ≈⟨ (+≫ *-assoc _ _ _ ⊙ sym (distribˡ _ _ _)) ⟨ +-cong ⟩
        (*-assoc _ _ _ ⊙ *≫ *-comm _ _ ⊙ sym (*-assoc _ _ _)) ⟩
        x′ * (y′ + ys′ * ρ) + xs′ * ρ * (y′ + ys′ * ρ)
      ≈⟨ sym (distribʳ _ _ _) ⟩
        (x′ + xs′ * ρ) * (y′ + ys′ * ρ)
      ∎ }

  ⊠-coeffs-hom : ∀ {n}
               → (a : Acc _<′_ n)
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
      Σ⟦ para (⊠-cons a y ys) xs ⍓ j ⟧ (ρ , Ρ)
    ≈⟨ sym (pow-hom j (para (⊠-cons a y ys) xs) ρ Ρ) ⟩
      Σ⟦ para (⊠-cons a y ys) xs ⟧ (ρ , Ρ) * ρ ^ j
    ≈⟨ ≪* ⊠-cons-hom a y ys xs ρ Ρ ⟩
      xs′ * (y′ + ys′ * ρ) * ρ ^ j
    ≈⟨ *-assoc _ _ _ ⟩
      xs′ * ((y′ + ys′ * ρ) * ρ ^ j)
    ∎

  ⊠-inj-hom : ∀ {i k}
            → (a : Acc _<′_ k)
            → (i≤k : i ≤′ k)
            → (x : FlatPoly i)
            → (xs : Coeffs k)
            → (ρ : Carrier)
            → (Ρ : Vec Carrier k)
            → Σ⟦ para (⊠-inj a i≤k x) xs ⟧ (ρ , Ρ) ≈ ⟦ x Π i≤k ⟧ Ρ * Σ⟦ xs ⟧ (ρ , Ρ)
  ⊠-inj-hom a i≤k x xs ρ Ρ = poly-foldR ρ Ρ (⊠-inj a i≤k x) (⟦ x Π i≤k ⟧ Ρ *_) (*-assoc _) inj-step (sym (zeroʳ _)) xs
    where
    inj-step = λ { (y Π j≤k) {ys} zs ys≋zs →
      let x′  = ⟦ x Π i≤k ⟧ Ρ
          y′  = ⟦ y Π j≤k ⟧ Ρ
          zs′ = Σ⟦ zs ⟧ (ρ , Ρ)
      in
      begin
        ⟦ ⊠-match a (inj-compare i≤k j≤k) x y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ
      ≈⟨ ⊠-match-hom a (inj-compare i≤k j≤k) x _ Ρ ⟨ +-cong ⟩ (≪* ys≋zs ⊙ *-assoc _ _ _) ⟩
        x′ * y′ + x′ * (zs′ * ρ)
      ≈⟨ sym (distribˡ x′ _ _ ) ⟩
        x′ * (y′ + zs′ * ρ)
      ∎ }

⊠-hom : ∀ {n}
      → (xs : Poly n)
      → (ys : Poly n)
      → (Ρ : Vec Carrier n)
      → ⟦ xs ⊠ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ * ⟦ ys ⟧ Ρ
⊠-hom = ⊠-step-hom (<′-wellFounded _)
