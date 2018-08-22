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
open import Level using (Lift; lower; lift)
open import Data.Fin as Fin using (Fin)
open Coeff

mutual
  ⊞-hom : ∀ {n}
        → (xs : Poly n)
        → (ys : Poly n)
        → (Ρ : Vec Carrier n)
        → ⟦ xs ⊞ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ + ⟦ ys ⟧ Ρ
  ⊞-hom (xs Π i≤n) (ys Π j≤n) = ⊞-match-hom (i≤n ∺ j≤n) xs ys

  ⊞-match-hom : ∀ {i j n}
              → {i≤n : i ≤ n}
              → {j≤n : j ≤ n}
              → (cmp : Ordering i≤n j≤n)
              → (xs : FlatPoly i)
              → (ys : FlatPoly j)
              → (Ρ : Vec Carrier n)
              → ⟦ ⊞-match cmp xs ys ⟧ Ρ ≈ ⟦ xs Π i≤n ⟧ Ρ + ⟦ ys Π j≤n ⟧ Ρ
  ⊞-match-hom (eq ij≤n) (Κ x) (Κ y) Ρ = +-homo x y
  ⊞-match-hom (eq ij≤n) (Σ xs) (Σ ys) Ρ =
    begin
      ⟦ ⊞-coeffs xs ys Π↓ ij≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊞-coeffs xs ys) ij≤n Ρ ⟩
      Σ⟦ ⊞-coeffs xs ys ⟧ (drop-1 ij≤n Ρ)
    ≈⟨ ⊞-coeffs-hom xs ys (drop-1 ij≤n Ρ) ⟩
      Σ⟦ xs ⟧ (drop-1 ij≤n Ρ) + Σ⟦ ys ⟧ (drop-1 ij≤n Ρ)
    ∎
  ⊞-match-hom (i≤n > j≤i-1) (Σ xs) ys Ρ =
    let (ρ , Ρ′) = drop-1 i≤n Ρ
    in
    begin
      ⟦ ⊞-inj j≤i-1 ys xs Π↓ i≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊞-inj j≤i-1 ys xs) i≤n Ρ ⟩
      Σ⟦ ⊞-inj j≤i-1 ys xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ⊞-inj-hom j≤i-1 ys xs ρ Ρ′ ⟩
      ⟦ ys Π j≤i-1 ⟧ (proj₂ (drop-1 i≤n Ρ)) + Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ≪+ ⋈-hom j≤i-1 i≤n ys Ρ ⟩
      ⟦ ys Π (j≤i-1 ⋈ i≤n) ⟧ Ρ + Σ⟦ xs ⟧ (drop-1 i≤n Ρ)
    ≈⟨ +-comm _ _ ⟩
      Σ⟦ xs ⟧ (drop-1 i≤n Ρ) + ⟦ ys Π (j≤i-1 ⋈ i≤n) ⟧ Ρ
    ∎
  ⊞-match-hom (i≤j-1 < j≤n) xs (Σ ys) Ρ =
    let (ρ , Ρ′) = drop-1 j≤n Ρ
    in
    begin
      ⟦ ⊞-inj i≤j-1 xs ys Π↓ j≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊞-inj i≤j-1 xs ys) j≤n Ρ ⟩
      Σ⟦ ⊞-inj i≤j-1 xs ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ⊞-inj-hom i≤j-1 xs ys ρ Ρ′ ⟩
      ⟦ xs Π i≤j-1 ⟧ (proj₂ (drop-1 j≤n Ρ)) + Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ≪+ ⋈-hom i≤j-1 j≤n xs Ρ ⟩
      ⟦ xs Π (i≤j-1 ⋈ j≤n) ⟧ Ρ + Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ∎

  ⊞-inj-hom : ∀ {i k}
            → (i≤k : i ≤ k)
            → (x : FlatPoly i)
            → (ys : Coeffs k)
            → (ρ : Carrier)
            → (Ρ : Vec Carrier k)
            → Σ⟦ ⊞-inj i≤k x ys ⟧ (ρ , Ρ) ≈ ⟦ x Π i≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ)
  ⊞-inj-hom i≤k xs [] ρ Ρ =
    begin
      Σ⟦ (xs Π i≤k) ^ zero ∷↓ [] ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom (xs Π i≤k) zero [] ρ Ρ ⟩
      (⟦ xs Π i≤k ⟧ Ρ + Σ⟦ [] ⟧ (ρ , Ρ) * ρ) * ρ ^ zero
    ≈⟨ *-identityʳ _ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + Σ⟦ [] ⟧ (ρ , Ρ) * ρ
    ≈⟨ +≫ zeroˡ ρ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + Σ⟦ [] ⟧ (ρ , Ρ)
    ∎
  ⊞-inj-hom i≤k xs (y Π j≤k ≠0 Δ zero ∷ ys) ρ Ρ =
    begin
      Σ⟦ ⊞-match (j≤k ∺ i≤k) y xs ^ zero ∷↓ ys ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom (⊞-match (j≤k ∺ i≤k) y xs) zero ys ρ Ρ ⟩
      (⟦ ⊞-match (j≤k ∺ i≤k) y xs ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ zero
    ≈⟨ ≪* ≪+ ⊞-match-hom (j≤k ∺ i≤k) y xs Ρ ⟩
      (⟦ y Π j≤k ⟧ Ρ + ⟦ xs Π i≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ zero
    ≈⟨ ≪* ≪+ +-comm _ _ ⟩
      (⟦ xs Π i≤k ⟧ Ρ + ⟦ y Π j≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ zero
    ≈⟨ ≪* +-assoc _ _ _ ⟩
      (⟦ xs Π i≤k ⟧ Ρ + (⟦ y Π j≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ)) * ρ ^ zero
    ≈⟨ distribʳ (ρ ^ zero) _ _ ⟩
      ⟦ xs Π i≤k ⟧ Ρ * ρ ^ zero + (⟦ y Π j≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ zero
    ≈⟨ ≪+ *-identityʳ _ ⟩
      ⟦ xs Π i≤k ⟧ Ρ + (⟦ y Π j≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ zero
    ∎
  ⊞-inj-hom i≤k xs (y Δ suc j ∷ ys) ρ Ρ =
    let y′ = poly y
    in
    begin
      Σ⟦ ⊞-inj i≤k xs (y Δ suc j ∷ ys) ⟧ (ρ , Ρ)
    ≡⟨⟩
      Σ⟦ xs Π i≤k ^ zero ∷↓ y Δ j ∷ ys ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom (xs Π i≤k) zero (y Δ j ∷ ys) ρ Ρ ⟩
      (⟦ xs Π i≤k ⟧ Ρ + Σ⟦ y Δ j ∷ ys ⟧ (ρ , Ρ) * ρ) * ρ ^ zero
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
              → (Ρ : Carrier × Vec Carrier n)
              → Σ⟦ ⊞-coeffs xs ys ⟧ Ρ ≈ Σ⟦ xs ⟧ Ρ + Σ⟦ ys ⟧ Ρ
  ⊞-coeffs-hom [] ys Ρ = sym (+-identityˡ (Σ⟦ ys ⟧ Ρ))
  ⊞-coeffs-hom (x Δ i ∷ xs) = ⊞-zip-r-hom i x xs

  ⊞-zip-hom : ∀ {n i j}
           → (c : ℕ.Ordering i j)
           → (x : Coeff n)
           → (xs : Coeffs n)
           → (y : Coeff n)
           → (ys : Coeffs n)
           → (Ρ : Carrier × Vec Carrier n)
           → Σ⟦ ⊞-zip c x xs y ys ⟧ Ρ
           ≈ Σ⟦ x Δ i ∷ xs ⟧ Ρ + Σ⟦ y Δ j ∷ ys ⟧ Ρ
  ⊞-zip-hom (ℕ.equal i) x xs y ys (ρ , Ρ) =
    let x′  = ⟦ poly x ⟧ Ρ
        y′  = ⟦ poly y ⟧ Ρ
        xs′ = Σ⟦ xs ⟧ (ρ , Ρ)
        ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      Σ⟦ poly x ⊞ poly y ^ i ∷↓ ⊞-coeffs xs ys ⟧ (ρ , Ρ)
    ≈⟨ ∷↓-hom (poly x ⊞ poly y) i (⊞-coeffs xs ys) ρ Ρ ⟩
      (⟦ poly x ⊞ poly y ⟧ Ρ + Σ⟦ ⊞-coeffs xs ys ⟧ (ρ , Ρ) * ρ) * ρ ^ i
    ≈⟨ ≪* begin
            ⟦ poly x ⊞ poly y ⟧ Ρ + Σ⟦ ⊞-coeffs xs ys ⟧ (ρ , Ρ) * ρ
          ≈⟨ ⊞-hom (poly x) (poly y) Ρ ⟨ +-cong ⟩ (≪* ⊞-coeffs-hom xs ys (ρ , Ρ)) ⟩
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
  ⊞-zip-hom (ℕ.less i k) x xs y ys (ρ , Ρ) = ⊞-zip-r-step-hom i k y ys x xs (ρ , Ρ) ︔ +-comm _ _
  ⊞-zip-hom (ℕ.greater j k) = ⊞-zip-r-step-hom j k

  ⊞-zip-r-step-hom : ∀ {n} j k
                  → (x : Coeff n)
                  → (xs : Coeffs n)
                  → (y : Coeff n)
                  → (ys : Coeffs n)
                  → (Ρ : Carrier × Vec Carrier n)
                  → Σ⟦ y Δ j ∷ ⊞-zip-r x k xs ys ⟧ ( Ρ)
                  ≈ Σ⟦ x Δ suc (j ℕ.+ k) ∷ xs ⟧ ( Ρ) + Σ⟦ y Δ j ∷ ys ⟧ ( Ρ)
  ⊞-zip-r-step-hom j k x xs y ys (ρ , Ρ) =
    let x′  = ⟦ poly x ⟧ Ρ
        y′  = ⟦ poly y ⟧ Ρ
        xs′ = Σ⟦ xs ⟧ (ρ , Ρ)
        ys′ = Σ⟦ ys ⟧ (ρ , Ρ)
    in
    begin
      (y′ + Σ⟦ ⊞-zip-r x k xs ys ⟧ (ρ , Ρ) * ρ) * ρ ^ j
    ≈⟨ ≪* +≫ ≪* ⊞-zip-r-hom k x xs ys (ρ , Ρ) ⟩
      (y′ + ((x′ + xs′ * ρ) * ρ ^ k + ys′) * ρ) * ρ ^ j
    ≈⟨ ≪* +≫ distribʳ ρ _ _ ⟩
      (y′ + ((x′ + xs′ * ρ) * ρ ^ k * ρ + ys′ * ρ)) * ρ ^ j
    ≈⟨ ≪* (sym (+-assoc _ _ _) ︔ ≪+ +-comm _ _ ︔ +-assoc _ _ _) ⟩
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
                  ≡⟨ ≡.cong (ρ ^_) (ℕ-≡.+-comm k (suc j)) ⟩
                    ρ ^ suc (j ℕ.+ k)
                  ∎ ⟩
             (x′ + xs′ * ρ) * ρ ^ suc (j ℕ.+ k)
           ∎ ⟩
      (x′ + xs′ * ρ) * ρ ^ suc (j ℕ.+ k) + (y′ + ys′ * ρ) * ρ ^ j
    ∎

  ⊞-zip-r-hom : ∀ {n} i
             → (x : Coeff n)
             → (xs : Coeffs n)
             → (ys : Coeffs n)
             → (Ρ : Carrier × Vec Carrier n)
             → Σ⟦ ⊞-zip-r x i xs ys ⟧ (Ρ) ≈ Σ⟦ x Δ i ∷ xs ⟧ ( Ρ) + Σ⟦ ys ⟧ ( Ρ)
  ⊞-zip-r-hom i x xs [] (ρ , Ρ) = sym (+-identityʳ _)
  ⊞-zip-r-hom i x xs ((y Δ j) ∷ ys) = ⊞-zip-hom (ℕ.compare i j) x xs y ys
