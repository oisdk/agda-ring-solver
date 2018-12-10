{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters

module Polynomial.Homomorphism.Addition
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open import Function

open import Data.Nat as ℕ using (ℕ; suc; zero; compare)
open import Data.Product  using (_,_; _×_; proj₂)
open import Data.List     using (_∷_; [])
open import Data.Vec      using (Vec)

import Data.Nat.Properties as ℕ-Prop
import Relation.Binary.PropositionalEquality as ≡
import Relation.Binary.PropositionalEquality.TrustMe as TrustMe

open Homomorphism homo
open import Polynomial.Homomorphism.Lemmas homo
open import Polynomial.NormalForm homo
open import Polynomial.Reasoning ring

open import Polynomial.Exponentiation rawRing

open import Relation.Unary
open import Reader

mutual
  ⊞-hom : ∀ {n}
        → (xs : Poly n)
        → (ys : Poly n)
        → Π[ ⦇ ⟦ xs ⊞ ys ⟧ ≈ ⦇ ⟦ xs ⟧ + ⟦ ys ⟧ ⦈ ⦈ ]
  ⊞-hom (xs Π i≤n) (ys Π j≤n) = ⊞-match-hom (inj-compare i≤n j≤n) xs ys

  ⊞-match-hom : ∀ {i j n}
              → {i≤n : i ≤′ n}
              → {j≤n : j ≤′ n}
              → (i-cmp-j : InjectionOrdering i≤n j≤n)
              → (xs : FlatPoly i)
              → (ys : FlatPoly j)
              → Π[ ⦇ ⟦ ⊞-match i-cmp-j xs ys ⟧ ≈ ⦇ ⟦ xs Π i≤n ⟧ + ⟦ ys Π j≤n ⟧ ⦈ ⦈ ]
  ⊞-match-hom (inj-eq ij≤n) (Κ x) (Κ y) Ρ = +-homo x y
  ⊞-match-hom (inj-eq ij≤n) (Σ xs) (Σ ys) Ρ =
    begin
      ⟦ ⊞-coeffs xs ys Π↓ ij≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊞-coeffs xs ys) ij≤n Ρ ⟩
      Σ⟦ ⊞-coeffs xs ys ⟧ (drop-1 ij≤n Ρ)
    ≈⟨ ⊞-coeffs-hom xs ys (drop-1 ij≤n Ρ) ⟩
      Σ⟦ xs ⟧ (drop-1 ij≤n Ρ) + Σ⟦ ys ⟧ (drop-1 ij≤n Ρ)
    ∎
  ⊞-match-hom (inj-gt i≤n j≤i-1) (Σ xs) ys Ρ =
    let (ρ , Ρ′) = drop-1 i≤n Ρ
    in
    begin
      ⟦ ⊞-inj j≤i-1 ys xs Π↓ i≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊞-inj j≤i-1 ys xs) i≤n Ρ ⟩
      Σ⟦ ⊞-inj j≤i-1 ys xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ⊞-inj-hom j≤i-1 ys xs ρ Ρ′ ⟩
      ⟦ ys Π j≤i-1 ⟧ (proj₂ (drop-1 i≤n Ρ)) + Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ≪+ trans-join-hom j≤i-1 i≤n ys Ρ ⟩
      ⟦ ys Π (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n) ⟧ Ρ + Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ +-comm _ _ ⟩
      Σ⟦ xs ⟧ (drop-1 i≤n Ρ) + ⟦ ys Π (≤′-step j≤i-1 ⟨ ≤′-trans ⟩ i≤n) ⟧ Ρ
    ∎
  ⊞-match-hom (inj-lt i≤j-1 j≤n) xs (Σ ys) Ρ =
    let (ρ , Ρ′) = drop-1 j≤n Ρ
    in
    begin
      ⟦ ⊞-inj i≤j-1 xs ys Π↓ j≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊞-inj i≤j-1 xs ys) j≤n Ρ ⟩
      Σ⟦ ⊞-inj i≤j-1 xs ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ⊞-inj-hom i≤j-1 xs ys ρ Ρ′ ⟩
      ⟦ xs Π i≤j-1 ⟧ (proj₂ (drop-1 j≤n Ρ)) + Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ≪+ trans-join-hom i≤j-1 j≤n xs Ρ ⟩
      ⟦ xs Π (≤′-step i≤j-1 ⟨ ≤′-trans ⟩ j≤n) ⟧ Ρ + Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ∎

  ⊞-inj-hom : ∀ {i k}
            → (i≤k : i ≤′ k)
            → (x : FlatPoly i)
            → (ys : Coeffs k)
            → (ρ : Carrier)
            → (Ρ : Vec Carrier k)
            → Σ⟦ ⊞-inj i≤k x ys ⟧ (ρ , Ρ) ≈ ⟦ x Π i≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ)
  ⊞-inj-hom i≤k xs [] ρ Ρ =
    begin
      Σ⟦ (xs Π i≤k) Δ 0 ∷↓ [] ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom (xs Π i≤k) 0 [] ρ Ρ ⟩
      (⟦ xs Π i≤k ⟧ Ρ + Σ⟦ [] ⟧ (ρ , Ρ) * ρ) * ρ ^ 0
    ≈⟨ *-identityʳ _ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + Σ⟦ [] ⟧ (ρ , Ρ) * ρ
    ≈⟨ +≫ zeroˡ ρ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + Σ⟦ [] ⟧ (ρ , Ρ)
    ∎
  ⊞-inj-hom i≤k xs (y Π j≤k ≠0 Δ 0 ∷ ys) ρ Ρ =
    begin
      Σ⟦ ⊞-match (inj-compare j≤k i≤k) y xs Δ 0 ∷↓ ys ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom (⊞-match (inj-compare j≤k i≤k) y xs) 0 ys ρ Ρ ⟩
      (⟦ ⊞-match (inj-compare j≤k i≤k) y xs ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ 0
    ≈⟨ ≪* ≪+ ⊞-match-hom (inj-compare j≤k i≤k) y xs Ρ ⟩
      (⟦ y Π j≤k ⟧ Ρ + ⟦ xs Π i≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ 0
    ≈⟨ ≪* ≪+ +-comm _ _ ⟩
      (⟦ xs Π i≤k ⟧ Ρ + ⟦ y Π j≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ 0
    ≈⟨ ≪* +-assoc _ _ _ ⟩
      (⟦ xs Π i≤k ⟧ Ρ + (⟦ y Π j≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ)) * ρ ^ 0
    ≈⟨ distribʳ (ρ ^ 0) _ _ ⟩
      ⟦ xs Π i≤k ⟧ Ρ * ρ ^ 0 + (⟦ y Π j≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ 0
    ≈⟨ ≪+ *-identityʳ _ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + (⟦ y Π j≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ 0
    ∎
  ⊞-inj-hom i≤k xs (y Δ suc j ∷ ys) ρ Ρ =
    let y′ = NonZero.poly y
    in
    begin
      Σ⟦ ⊞-inj i≤k xs (y Δ suc j ∷ ys) ⟧ (ρ , Ρ)
    ≡⟨⟩
      Σ⟦ xs Π i≤k Δ 0 ∷↓ y Δ j ∷ ys ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom (xs Π i≤k) 0 (y Δ j ∷ ys) ρ Ρ ⟩
      (⟦ xs Π i≤k ⟧ Ρ + Σ⟦ y Δ j ∷ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ 0
    ≈⟨ *-identityʳ _ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + Σ⟦ y Δ j ∷ ys ⟧ (ρ , Ρ) * ρ
    ≡⟨⟩
      ⟦ xs Π i≤k ⟧ Ρ + ((⟦ y′ ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ j ) * ρ
    ≈⟨ +≫  *-assoc _ _ ρ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + (⟦ y′ ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * (ρ ^ j  * ρ)
    ≈⟨ +≫ *≫  *-comm _ ρ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + (⟦ y′ ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ suc j
    ≡⟨⟩
      ⟦ xs Π i≤k ⟧ Ρ + Σ⟦ y Δ suc j ∷ ys ⟧ (ρ , Ρ)
    ∎

  ⊞-coeffs-hom : ∀ {n}
              → (xs : Coeffs n)
              → (ys : Coeffs n)
              → Π[ ⦇ Σ⟦ ⊞-coeffs xs ys ⟧ ≈ ⦇ Σ⟦ xs ⟧ + Σ⟦ ys ⟧ ⦈ ⦈ ]
  ⊞-coeffs-hom [] ys Ρ = sym (+-identityˡ (Σ⟦ ys ⟧ Ρ))
  ⊞-coeffs-hom (x Δ i ∷ xs) = ⊞-zip-r-hom i x xs

  ⊞-zip-hom : ∀ {n i j}
           → (c : ℕ.Ordering i j)
           → (x : NonZero n)
           → (xs : Coeffs n)
           → (y : NonZero n)
           → (ys : Coeffs n)
           → Π[ ⦇ Σ⟦ ⊞-zip c x xs y ys ⟧ ≈ ⦇ Σ⟦ x Δ i ∷ xs ⟧ + Σ⟦ y Δ j ∷ ys ⟧ ⦈ ⦈ ]
  ⊞-zip-hom (ℕ.equal i) (x ≠0) xs (y ≠0) ys (ρ , Ρ) =
    let x′  = ⟦ x ⟧ Ρ
        y′  = ⟦ y ⟧ Ρ
        xs′ = Σ⟦ xs ⟧ (ρ , Ρ)
        ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      Σ⟦ x ⊞ y Δ i ∷↓ ⊞-coeffs xs ys ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom (x ⊞ y) i (⊞-coeffs xs ys) ρ Ρ ⟩
      (⟦ x ⊞ y ⟧ Ρ + Σ⟦ ⊞-coeffs xs ys ⟧ (ρ , Ρ) * ρ) * ρ ^ i
    ≈⟨ ≪* begin
            ⟦ x ⊞ y ⟧ Ρ + Σ⟦ ⊞-coeffs xs ys ⟧ (ρ , Ρ) * ρ
          ≈⟨ ⊞-hom x y Ρ ⟨ +-cong ⟩ (≪* ⊞-coeffs-hom xs ys (ρ , Ρ)) ⟩
            (x′ + y′) + (xs′ + ys′) * ρ
          ≈⟨ +≫ distribʳ ρ _ _ ⟩
            (x′ + y′) + (xs′ * ρ + ys′ * ρ)
          ≈⟨ +-assoc x′ y′ _ ⟩
            x′ + (y′ + (xs′ * ρ + ys′ * ρ))
          ≈⟨ +≫ sym ( +-assoc y′ _ _ ) ⟩
            x′ + ((y′ + xs′ * ρ) + ys′ * ρ)
          ≈⟨ +≫ ≪+ +-comm y′ _ ⟩
            x′ + ((xs′ * ρ + y′) + ys′ * ρ)
          ≈⟨ +≫ +-assoc _ y′ _ ⟩
            x′ + (xs′ * ρ + (y′ + ys′ * ρ))
          ≈⟨ sym (+-assoc x′ _ _) ⟩
            (x′ + xs′ * ρ) + (y′ + ys′ * ρ)
          ∎ ⟩
      ((x′ + xs′ * ρ) + (y′ + ys′ * ρ)) * ρ ^ i
    ≈⟨ distribʳ (ρ ^ i) _ _ ⟩
      (x′ + xs′ * ρ) * ρ ^ i + (y′ + ys′ * ρ) * ρ ^ i
    ∎
  ⊞-zip-hom (ℕ.less i k) x xs y ys (ρ , Ρ) = ⊞-zip-r-step-hom i k y ys x xs (ρ , Ρ) ⊙ +-comm _ _
  ⊞-zip-hom (ℕ.greater j k) = ⊞-zip-r-step-hom j k

  ⊞-zip-r-step-hom : ∀ {n} j k
                  → (x : NonZero n)
                  → (xs : Coeffs n)
                  → (y : NonZero n)
                  → (ys : Coeffs n)
                  → Π[ ⦇ Σ⟦ y Δ j ∷ ⊞-zip-r x k xs ys ⟧ ≈ ⦇ Σ⟦ x Δ suc (j ℕ.+ k) ∷ xs ⟧ + Σ⟦ y Δ j ∷ ys ⟧ ⦈ ⦈ ]
  ⊞-zip-r-step-hom j k x xs y ys (ρ , Ρ) =
    let x′  = ⟦ NonZero.poly x ⟧ Ρ
        y′  = ⟦ NonZero.poly y ⟧ Ρ
        xs′ = Σ⟦ xs ⟧ (ρ , Ρ)
        ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      (y′ + Σ⟦ ⊞-zip-r x k xs ys ⟧ (ρ , Ρ) * ρ) * ρ ^ j
    ≈⟨ ≪* +≫ ≪* ⊞-zip-r-hom k x xs ys (ρ , Ρ) ⟩
      (y′ + ((x′ + xs′ * ρ) * ρ ^ k + ys′) * ρ) * ρ ^ j
    ≈⟨ ≪* +≫ distribʳ ρ _ _ ⟩
      (y′ + ((x′ + xs′ * ρ) * ρ ^ k * ρ + ys′ * ρ)) * ρ ^ j
    ≈⟨ ≪* (sym (+-assoc _ _ _) ⊙ ≪+ +-comm _ _ ⊙ +-assoc _ _ _) ⟩
      ((x′ + xs′ * ρ) * ρ ^ k * ρ + (y′ + ys′ * ρ)) * ρ ^ j
    ≈⟨ distribʳ (ρ ^ j) _ _ ⟩
      (x′ + xs′ * ρ) * ρ ^ k * ρ * ρ ^ j + (y′ + ys′ * ρ) * ρ ^ j
    ≈⟨ ≪+ begin
             (((x′ + xs′ * ρ) * ρ ^ k) * ρ) * ρ ^ j
           ≈⟨ *-assoc _ ρ (ρ ^ j) ⟩
             ((x′ + xs′ * ρ) * ρ ^ k) * (ρ * ρ ^ j)
           ≈⟨ *-assoc _ _ _ ⟩
             (x′ + xs′ * ρ) * (ρ ^ k * (ρ * ρ ^ j))
           ≈⟨ *≫ begin
                    ρ ^ k * (ρ * ρ ^ j)
                  ≈⟨ pow-add ρ k _ ⟩
                    ρ ^ (k ℕ.+ suc j)
                  ≡⟨ TrustMe.erase (≡.cong (ρ ^_) (ℕ-Prop.+-comm k (suc j))) ⟩
                    ρ ^ suc (j ℕ.+ k)
                  ∎ ⟩
             (x′ + xs′ * ρ) * ρ ^ suc (j ℕ.+ k)
           ∎ ⟩
      (x′ + xs′ * ρ) * ρ ^ suc (j ℕ.+ k) + (y′ + ys′ * ρ) * ρ ^ j
    ∎

  ⊞-zip-r-hom : ∀ {n} i
             → (x : NonZero n)
             → (xs : Coeffs n)
             → (ys : Coeffs n)
             → (Ρ : Carrier × Vec Carrier n)
             → Σ⟦ ⊞-zip-r x i xs ys ⟧ (Ρ) ≈ Σ⟦ x Δ i ∷ xs ⟧ ( Ρ) + Σ⟦ ys ⟧ ( Ρ)
  ⊞-zip-r-hom i x xs [] (ρ , Ρ) = sym (+-identityʳ _)
  ⊞-zip-r-hom i x xs ((y Δ j) ∷ ys) = ⊞-zip-hom (ℕ.compare i j) x xs y ys
