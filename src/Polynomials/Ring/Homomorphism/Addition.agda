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
open Coeff

mutual
  ⊞-hom : ∀ {n}
        → (xs : Poly n)
        → (ys : Poly n)
        → (Ρ : Vec Carrier n)
        → ⟦ xs ⊞ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ + ⟦ ys ⟧ Ρ
  ⊞-hom (xs Π i≤n) (ys Π j≤n) = ⊞-match-hom (≤-compare i≤n j≤n) xs i≤n ys j≤n

  ⊞-match-hom : ∀ {i j n}
              → (cmp : Ordering i j)
              → (xs : FlatPoly i)
              → (i≤n : i ≤ n)
              → (ys : FlatPoly j)
              → (j≤n : j ≤ n)
              → (Ρ : Vec Carrier n)
              → ⟦ ⊞-match cmp xs i≤n ys j≤n ⟧ Ρ ≈ ⟦ xs Π i≤n ⟧ Ρ + ⟦ ys Π j≤n ⟧ Ρ
  ⊞-match-hom equal (Κ x) i≤n (Κ y) j≤n Ρ = +-homo x y
  ⊞-match-hom equal (Σ xs) i≤n (Σ ys) j≤n Ρ =
    begin
      ⟦ ⊞-coeffs xs ys Π↓ i≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊞-coeffs xs ys) i≤n Ρ ⟩
      Σ⟦ ⊞-coeffs xs ys ⟧ (drop-1 i≤n Ρ)
    ≈⟨ ⊞-coeffs-hom xs ys (drop-1 i≤n Ρ) ⟩
      Σ⟦ xs ⟧ (drop-1 i≤n Ρ) + Σ⟦ ys ⟧ (drop-1 i≤n Ρ)
      ≡⟨ ≡.cong (λ iltn → Σ⟦ xs ⟧ (drop-1 i≤n Ρ) + Σ⟦ ys ⟧ (drop-1 iltn Ρ)) (≤-irrel i≤n j≤n) ⟩
      Σ⟦ xs ⟧ (drop-1 i≤n Ρ) + Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ∎
  ⊞-match-hom (greater j≤i-1) xs i≤n ys j≤n Ρ = {!!}
  ⊞-match-hom (less    i≤j-1) xs i≤n (Σ ys) j≤n Ρ =
    let (ρ , Ρ′) = drop-1 j≤n Ρ
    in
    begin
      ⟦ ⊞-inj i≤j-1 xs ys Π↓ j≤n ⟧ Ρ
    ≈⟨ Π↓-hom (⊞-inj i≤j-1 xs ys) j≤n Ρ ⟩
      Σ⟦ ⊞-inj i≤j-1 xs ys ⟧ (drop-1 j≤n Ρ)
    ≈⟨ ⊞-inj-hom i≤j-1 xs ys ρ Ρ′ ⟩
      ⟦ xs Π i≤j-1 ⟧ Ρ′ + Σ⟦ ys ⟧ (drop-1 j≤n Ρ)
    ≅⟨ ≪+_ ⟩
      ⟦ xs Π i≤j-1 ⟧ Ρ′
    ≈⟨ {!!} ⟩
      ⟦ xs Π i≤n ⟧ Ρ
    ∎

  ⊞-inj-hom : ∀ {i k}
            → (i≤k : i ≤ k)
            → (x : FlatPoly i)
            → (ys : Coeffs k)
            → (ρ : Carrier)
            → (Ρ : Vec Carrier k)
            → Σ⟦ ⊞-inj i≤k x ys ⟧ (ρ , Ρ) ≈ ⟦ x Π i≤k ⟧ Ρ + Σ⟦ ys ⟧ (ρ , Ρ)
  ⊞-inj-hom i≤k xs [] = {!!}
  ⊞-inj-hom i≤k xs (y Π j≤k ≠0 Δ zero ∷ ys) ρ Ρ = {!!}
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
