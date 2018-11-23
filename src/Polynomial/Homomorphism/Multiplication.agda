{-# OPTIONS --without-K #-}

open import Polynomial.Parameters

module Polynomial.Homomorphism.Multiplication
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Data.Nat as ℕ          using (ℕ; suc; zero)
open import Data.Pair.NonDependent using (_×_; _,_; proj₁; proj₂; map₁)
open import Data.List              using (_∷_; [])
open import Data.Vec               using (Vec)
open import Induction.WellFounded  using (Acc; acc)
open import Induction.Nat          using (<′-wellFounded)

open import Function

open import Polynomial.Homomorphism.Lemmas homo
open import Polynomial.Homomorphism.Addition homo
open import Polynomial.NormalForm homo

open Homomorphism homo
open import Polynomial.Reasoning ring

{-# TERMINATING #-}
mutual
  ⊠-step-hom : ∀ {i n}
             → (xs : FlatPoly i)
             → (i≤n : i ≤′ n)
             → (ys : Poly n)
             → ∀ ρ
             → ⟦ ⊠-step xs i≤n ys ⟧ ρ ≈ ⟦ xs Π i≤n ⟧ ρ * ⟦ ys ⟧ ρ
  ⊠-step-hom (Κ x) i≤n ys = ⊠-Κ-hom x ys
  ⊠-step-hom (Σ xs) i≤n ys = ⊠-Σ-hom xs i≤n ys

  ⊠-Κ-hom : ∀ {n}
          → ∀ x
          → (ys : Poly n)
          → ∀ ρ
          → ⟦ ⊠-Κ x ys ⟧ ρ ≈ ⟦ x ⟧ᵣ * ⟦ ys ⟧ ρ
  ⊠-Κ-hom x (Κ y  Π i≤n) ρ = *-homo x y
  ⊠-Κ-hom  x (Σ xs Π i≤n) ρ =
    begin
      ⟦ ⊠-Κ-inj  x xs Π↓ i≤n ⟧ ρ
    ≈⟨ Π↓-hom (⊠-Κ-inj  x xs) i≤n ρ ⟩
      Σ⟦ ⊠-Κ-inj  x xs ⟧ (drop-1 i≤n ρ)
    ≈⟨ ⊠-Κ-inj-hom  x xs (drop-1 i≤n ρ) ⟩
      ⟦ x ⟧ᵣ * Σ⟦ xs ⟧ (drop-1 i≤n ρ)
    ∎

  ⊠-Κ-inj-hom : ∀ {n}
              → (x : Raw.Carrier)
              → (xs : Coeffs n)
              → ∀ ρ
              → Σ⟦ ⊠-Κ-inj x xs ⟧ ρ ≈ ⟦ x ⟧ᵣ * Σ⟦ xs ⟧ ρ
  ⊠-Κ-inj-hom {n} x xs (ρ , Ρ) = poly-foldR ρ Ρ (map₁ (⊠-Κ x)) (⟦ x ⟧ᵣ *_) (*-assoc _) step (sym (zeroʳ _)) xs
    where
    step : (y : Poly n)
         → {ys : Coeffs n}
         → (zs : Coeffs n)
         → Σ⟦ ys ⟧ (ρ , Ρ) ≈ ⟦ x ⟧ᵣ * Σ⟦ zs ⟧ (ρ , Ρ)
         → (map₁ (⊠-Κ x) (y , ys) ⟦∷⟧ (ρ , Ρ)) ≈ ⟦ x ⟧ᵣ * ((y , zs) ⟦∷⟧ (ρ , Ρ))
    step y {ys} zs ys≋zs =
      begin
        map₁ (⊠-Κ x) (y , ys) ⟦∷⟧ (ρ , Ρ)
      ≡⟨⟩
        ⟦ ⊠-Κ x y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ
      ≈⟨ ⊠-Κ-hom x y Ρ ⟨ +-cong ⟩ (≪* ys≋zs ⊙ *-assoc _ _ _) ⟩
        ⟦ x ⟧ᵣ * ⟦ y ⟧ Ρ + ⟦ x ⟧ᵣ * (Σ⟦ zs ⟧ (ρ , Ρ) * ρ)
      ≈⟨ sym (distribˡ ⟦ x ⟧ᵣ _ _) ⟩
        ⟦ x ⟧ᵣ * (⟦ y ⟧ Ρ + Σ⟦ zs ⟧ (ρ , Ρ) * ρ)
      ≡⟨⟩
        ⟦ x ⟧ᵣ * ((y , zs) ⟦∷⟧ (ρ , Ρ))
      ∎

  ⊠-Σ-hom : ∀ {i n}
          → (xs : Coeffs i)
          → (i<n : i <′ n)
          → (ys : Poly n)
          → ∀ ρ
          → ⟦ ⊠-Σ xs i<n ys ⟧ ρ ≈ Σ⟦ xs ⟧ (drop-1 i<n ρ) * ⟦ ys ⟧ ρ
  ⊠-Σ-hom xs i<n (Σ ys Π j≤n) = ⊠-match-hom (inj-compare i<n j≤n) xs ys
  ⊠-Σ-hom  xs i<n (Κ y  Π _) ρ =
    begin
      ⟦ ⊠-Κ-inj  y xs Π↓ i<n ⟧ ρ
    ≈⟨ Π↓-hom (⊠-Κ-inj  y xs) i<n ρ ⟩
      Σ⟦ ⊠-Κ-inj  y xs ⟧ (drop-1 i<n ρ)
    ≈⟨ ⊠-Κ-inj-hom  y xs (drop-1 i<n ρ) ⟩
      ⟦ y ⟧ᵣ * Σ⟦ xs ⟧ (drop-1 i<n ρ)
    ≈⟨ *-comm _ _ ⟩
      Σ⟦ xs ⟧ (drop-1 i<n ρ) * ⟦ y ⟧ᵣ
    ∎

  ⊠-Σ-inj-hom : ∀ {i k}
              → (i<k : i <′ k)
              → (xs : Coeffs i)
              → (ys : Poly k)
              → ∀ ρ
              → ⟦ ⊠-Σ-inj i<k xs ys ⟧ ρ ≈ Σ⟦ xs ⟧ (drop-1 i<k ρ) * ⟦ ys ⟧ ρ
  ⊠-Σ-inj-hom i<k x (Σ ys Π j≤k) = ⊠-match-hom (inj-compare i<k j≤k) x ys
  ⊠-Σ-inj-hom  i<k x (Κ y Π j≤k) ρ =
    begin
      ⟦ ⊠-Κ-inj  y x Π↓ i<k ⟧ ρ
    ≈⟨ Π↓-hom (⊠-Κ-inj  y x) i<k ρ ⟩
      Σ⟦ ⊠-Κ-inj  y x ⟧ (drop-1 i<k ρ)
    ≈⟨ ⊠-Κ-inj-hom  y x (drop-1 i<k ρ) ⟩
      ⟦ y ⟧ᵣ * Σ⟦ x ⟧ (drop-1 i<k ρ)
    ≈⟨ *-comm _ _ ⟩
      Σ⟦ x ⟧ (drop-1 i<k ρ) * ⟦ y ⟧ᵣ
    ∎

  ⊠-match-step-hom : ∀ {i j n}
                   → (xs : Coeffs i)
                   → (i≤j-1 : suc i ≤′ j)
                   → (j≤n   : suc j ≤′ n)
                   → (Ρ′ : Vec Carrier n)
                   → (y : Poly j)
                   → {ys : Coeffs j}
                   → (zs : Coeffs j)
                   → Σ⟦ ys ⟧ (drop-1 j≤n Ρ′) ≈ Σ⟦ xs ⟧ (drop-1 (≤′-trans (≤′-step i≤j-1) j≤n) Ρ′) * Σ⟦ zs ⟧ (drop-1 j≤n Ρ′)
                   → map₁ (⊠-Σ-inj i≤j-1 xs) (y , ys) ⟦∷⟧ (drop-1 j≤n Ρ′)
                   ≈ Σ⟦ xs ⟧ (drop-1 (≤′-trans (≤′-step i≤j-1) j≤n) Ρ′) * ((y , zs) ⟦∷⟧ (drop-1 j≤n Ρ′))
  ⊠-match-step-hom xs i≤j-1 j≤n Ρ′ y {ys} zs ys≋zs =
    let (ρ , Ρ) = drop-1 j≤n Ρ′
        xs′ = Σ⟦ xs ⟧ (drop-1 (≤′-trans (≤′-step i≤j-1) j≤n) Ρ′)
    in
    begin
      map₁ (⊠-Σ-inj i≤j-1 xs) (y , ys) ⟦∷⟧ (ρ , Ρ)
    ≡⟨⟩
      (⊠-Σ-inj i≤j-1 xs y , ys) ⟦∷⟧ (ρ , Ρ)
    ≡⟨⟩
      ⟦ ⊠-Σ-inj i≤j-1 xs y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ
    ≈⟨ ≪+ ⊠-Σ-inj-hom i≤j-1 xs y Ρ ⟩
      Σ⟦ xs ⟧ (drop-1 i≤j-1 Ρ) * ⟦ y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ
    ≈⟨ ≪+ ≪* trans-join-coeffs-hom i≤j-1 j≤n xs Ρ′ ⟩
      xs′ * ⟦ y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ
    ≈⟨ +≫ ≪* ys≋zs ⟩
      xs′ * ⟦ y ⟧ Ρ + (xs′ * Σ⟦ zs ⟧ (ρ , Ρ)) * ρ
    ≈⟨ +≫ *-assoc _ _ _ ⟩
      xs′ * ⟦ y ⟧ Ρ + xs′ * (Σ⟦ zs ⟧ (ρ , Ρ) * ρ)
    ≈⟨ sym (distribˡ xs′ _ _) ⟩
      xs′ * ((y , zs) ⟦∷⟧ (ρ , Ρ))
    ∎

  ⊠-match-hom : ∀ {i j n}
              → {i<n : i <′ n}
              → {j<n : j <′ n}
              → (ord : InjectionOrdering i<n j<n)
              → (xs : Coeffs i)
              → (ys : Coeffs j)
              → (Ρ : Vec Carrier n)
              → ⟦ ⊠-match ord xs ys ⟧ Ρ ≈ Σ⟦ xs ⟧ (drop-1 i<n Ρ) * Σ⟦ ys ⟧ (drop-1 j<n Ρ)
  ⊠-match-hom {j = j}  (inj-lt i≤j-1 j≤n) xs ys Ρ′ =
    let (ρ , Ρ) = drop-1 j≤n Ρ′
        xs′ = Σ⟦ xs ⟧ (drop-1 (≤′-trans (≤′-step i≤j-1) j≤n) Ρ′)
    in
    begin
      ⟦ para (map₁ (⊠-Σ-inj  i≤j-1 xs)) ys Π↓ j≤n ⟧ Ρ′
    ≈⟨ Π↓-hom (para (map₁ (⊠-Σ-inj  i≤j-1 xs)) ys) j≤n Ρ′ ⟩
      Σ⟦ para (map₁ (⊠-Σ-inj  i≤j-1 xs)) ys ⟧ (ρ , Ρ)
    ≈⟨ poly-foldR ρ Ρ (map₁ (⊠-Σ-inj  i≤j-1 xs)) (xs′ *_) (*-assoc _) (⊠-match-step-hom xs i≤j-1 j≤n  Ρ′) (sym (zeroʳ _)) ys ⟩
      xs′ * Σ⟦ ys ⟧ (ρ , Ρ)
    ∎
  ⊠-match-hom  (inj-gt i≤n j≤i-1) xs ys Ρ′ =
    let (ρ , Ρ) = drop-1 i≤n Ρ′
        ys′ = Σ⟦ ys ⟧ (drop-1 (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n) Ρ′)
    in
    begin
      ⟦ para (map₁ (⊠-Σ-inj  j≤i-1 ys)) xs Π↓ i≤n ⟧ Ρ′
    ≈⟨ Π↓-hom (para (map₁ (⊠-Σ-inj  j≤i-1 ys)) xs) i≤n Ρ′ ⟩
      Σ⟦ para (map₁ (⊠-Σ-inj  j≤i-1 ys)) xs ⟧ (ρ , Ρ)
    ≈⟨ poly-foldR ρ Ρ (map₁ (⊠-Σ-inj  j≤i-1 ys)) (ys′ *_) (*-assoc _) (⊠-match-step-hom ys j≤i-1 i≤n  Ρ′) (sym (zeroʳ _)) xs ⟩
      ys′ * Σ⟦ xs ⟧ (ρ , Ρ)
    ≈⟨ *-comm ys′ _ ⟩
      Σ⟦ xs ⟧ (ρ , Ρ) * ys′
    ∎
  ⊠-match-hom  (inj-eq ij≤n) xs ys Ρ =
    begin
      ⟦ ⊠-coeffs  xs ys Π↓ ij≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊠-coeffs  xs ys) ij≤n Ρ ⟩
      Σ⟦ ⊠-coeffs  xs ys ⟧ (drop-1 ij≤n Ρ)
    ≈⟨ ⊠-coeffs-hom  xs ys (drop-1 ij≤n Ρ) ⟩
      Σ⟦ xs ⟧ (drop-1 ij≤n Ρ) * Σ⟦ ys ⟧ (drop-1 ij≤n Ρ)
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
      Σ⟦ para (⊠-cons y ys) xs ⍓ j ⟧ (ρ , Ρ)
    ≈⟨ sym (pow-hom j (para (⊠-cons y ys) xs) ρ Ρ) ⟩
      Σ⟦ para (⊠-cons y ys) xs ⟧ (ρ , Ρ) * ρ ^ j
    ≈⟨ ≪* ⊠-cons-hom y ys xs ρ Ρ ⟩
      xs′ * (y′ + ys′ * ρ) * ρ ^ j
    ≈⟨ *-assoc _ _ _ ⟩
      xs′ * ((y′ + ys′ * ρ) * ρ ^ j)
    ∎

  ⊠-cons-hom : ∀ {n}
             → (y : Poly n)
             → (ys : Coeffs n)
             → (xs : Coeffs n)
             → (ρ : Carrier)
             → (Ρ : Vec Carrier n)
             → Σ⟦ para (⊠-cons y ys) xs ⟧ (ρ , Ρ)
             ≈ Σ⟦ xs ⟧ (ρ , Ρ) * (⟦ y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ)
  ⊠-cons-hom y ys xs ρ Ρ = poly-foldR ρ Ρ (⊠-cons y ys) (_* (⟦ y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ)) dist step base xs
    where
    dist = λ x y → *-assoc x _ y ⟨ trans ⟩ (*≫ *-comm _ y) ⟨ trans ⟩ sym (*-assoc x y _)
    base = sym (zeroˡ _)
    step = λ { (z Π j≤n) {ys₁} zs ys≋zs →
      let x′  = ⟦ z Π j≤n ⟧ Ρ
          xs′ = Σ⟦ zs ⟧ (ρ , Ρ)
          y′  = ⟦ y ⟧ Ρ
          ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
          step = λ y {ys} zs ys≋zs →
            begin
              map₁ (⊠-step z j≤n) (y , ys) ⟦∷⟧ (ρ , Ρ)
            ≡⟨⟩
              (⊠-step z j≤n y , ys) ⟦∷⟧ (ρ , Ρ)
            ≡⟨⟩
              ⟦ ⊠-step z j≤n y ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ
            ≈⟨ ⊠-step-hom z j≤n y Ρ ⟨ +-cong ⟩ (≪* ys≋zs ⊙ *-assoc _ _ _) ⟩
              ⟦ z Π j≤n ⟧ Ρ * ⟦ y ⟧ Ρ + ⟦ z Π j≤n ⟧ Ρ * (Σ⟦ zs ⟧ (ρ , Ρ) * ρ)
            ≈⟨ sym (distribˡ (⟦ z Π j≤n ⟧ Ρ) _ _) ⟩
              ⟦ z Π j≤n ⟧ Ρ * ((y , zs) ⟦∷⟧ (ρ , Ρ))
            ∎
      in
      begin
        ⟦ ⊠-step z j≤n y ⟧ Ρ + Σ⟦ ⊞-coeffs (para (map₁ (⊠-step z j≤n)) ys) ys₁ ⟧ (ρ , Ρ) * ρ
      ≈⟨ ⊠-step-hom z j≤n y Ρ ⟨ +-cong ⟩ (≪* ⊞-coeffs-hom (para (map₁ (⊠-step z j≤n)) ys) _ (ρ , Ρ)) ⟩
        x′ * y′ + (Σ⟦ para (map₁ (⊠-step z j≤n)) ys ⟧ (ρ , Ρ) + Σ⟦ ys₁ ⟧ (ρ , Ρ)) * ρ
      ≈⟨ +≫ ≪* (poly-foldR ρ Ρ (map₁ (⊠-step z j≤n)) (x′ *_) (*-assoc _) step (sym (zeroʳ _)) ys  ⟨ +-cong ⟩ ys≋zs) ⟩
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

⊠-hom : ∀ {n}
      → (xs : Poly n)
      → (ys : Poly n)
      → (Ρ : Vec Carrier n)
      → ⟦ xs ⊠ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ * ⟦ ys ⟧ Ρ
⊠-hom (xs Π i≤n) = ⊠-step-hom xs i≤n
