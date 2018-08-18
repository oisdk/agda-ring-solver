{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Ring.Homomorphism
  {r₁ r₂ r₃ r₄}
  (coeff : RawRing r₁)
  (Zero-C : Pred (RawRing.Carrier coeff) r₂)
  (zero-c? : Decidable Zero-C)
  (ring : AlmostCommutativeRing r₃ r₄)
  (morphism : coeff -Raw-AlmostCommutative⟶ ring)
  (Zero-C⟶Zero-R : ∀ x → Zero-C x → AlmostCommutativeRing._≈_ ring (_-Raw-AlmostCommutative⟶_.⟦_⟧ morphism x) (AlmostCommutativeRing.0# ring))
  where

open AlmostCommutativeRing ring
open import Polynomials.Ring.Reasoning ring
open import Polynomials.Ring.Normal coeff Zero-C zero-c?
open import Polynomials.Ring.Semantics coeff Zero-C zero-c? ring morphism
open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧ᵣ)
module Raw = RawRing coeff

open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product
import Data.Nat.Properties as ℕ-≡
import Relation.Binary.PropositionalEquality as ≡
open import Function
open import Data.List as List using (_∷_; [])
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Product.Irrelevant
open import Level using (Lift; lower; lift)
open import Data.Fin as Fin using (Fin)

pow-add : ∀ x i j → x ^ i * x ^ j ≈ x ^ (i ℕ.+ j)
pow-add x zero j = *-identityˡ (x ^ j)
pow-add x (suc i) j =
  begin
    x ^ suc i * x ^ j
  ≡⟨⟩
    (x * x ^ i) * x ^ j
  ≈⟨ *-assoc x _ _ ⟩
    x * (x ^ i * x ^ j)
  ≈⟨ *≫ pow-add x i j ⟩
    x * x ^ (i ℕ.+ j)
  ≡⟨⟩
    x ^ suc (i ℕ.+ j)
  ∎

pow-hom : ∀ {n} i
        → (xs : Coeffs n)
        → (ρ : Carrier)
        → (Ρ : Vec Carrier n)
        → ⟦ xs ⟧ (ρ ∷ Ρ) * ρ ^ i ≈ ⟦ xs ⍓ i ⟧ (ρ ∷ Ρ)
pow-hom i [] ρ Ρ = zeroˡ (ρ ^ i)
pow-hom i ((x , j) ∷ xs) ρ Ρ = *-assoc _ (ρ ^ j) (ρ ^ i) ︔ *≫ pow-add ρ j i

zero-hom : ∀ {n} (p : Poly n) → Zero n p → (Ρ : Vec Carrier n) → ⟦ p ⟧ Ρ ≈ 0#
zero-hom {zero} (lift p) p=0 [] = Zero-C⟶Zero-R p p=0
zero-hom {suc n} [] p=0 (x ∷ Ρ) = refl
zero-hom {suc n} (x ∷ p) (lift ()) Ρ

∷↓-hom : ∀ {n}
       → (x : Poly n)
       → (i : ℕ)
       → (xs : Poly (suc n))
       → (ρ : Carrier)
       → (Ρ : Vec Carrier n)
       → ⟦ (x , i) ∷↓ xs ⟧ (ρ ∷ Ρ) ≈ (⟦ x ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
∷↓-hom x i xs ρ Ρ with zero? x
∷↓-hom x i xs ρ Ρ | no ¬p = refl
∷↓-hom x i xs ρ Ρ | yes p =
  begin
    ⟦ xs ⍓ suc i ⟧ (ρ ∷ Ρ)
  ≈⟨ sym (pow-hom _ xs ρ Ρ) ⟩
    ⟦ xs ⟧ (ρ ∷ Ρ) * ρ ^ (suc i)
  ≈⟨ sym (*-assoc _ ρ _) ⟩
    ⟦ xs ⟧ (ρ ∷ Ρ) * ρ * ρ ^ i
  ≈⟨ ≪* (sym (+-identityˡ _) ︔ ≪+ sym (zero-hom x p _)) ⟩
    (⟦ x ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
  ∎

mutual
  ⊞-hom : ∀ {n}
        → (xs : Poly n)
        → (ys : Poly n)
        → (Ρ : Vec Carrier n)
        → ⟦ xs ⊞ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ + ⟦ ys ⟧ Ρ
  ⊞-hom {ℕ.zero} xs ys [] = +-homo _ _
  ⊞-hom {suc n} xs ys (ρ ∷ Ρ) = ⊞-coeffs-hom xs ys ρ Ρ

  ⊞-coeffs-hom : ∀ {n}
              → (xs : Coeffs n)
              → (ys : Coeffs n)
              → (ρ : Carrier)
              → (Ρ : Vec Carrier n)
              → ⟦ ⊞-coeffs xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ xs ⟧ (ρ ∷ Ρ) + ⟦ ys ⟧ (ρ ∷ Ρ)
  ⊞-coeffs-hom [] ys ρ Ρ = sym (+-identityˡ (⟦ ys ⟧ (ρ ∷ Ρ)))
  ⊞-coeffs-hom ((x , i) ∷ xs) = ⊞-ne-r-hom i x xs

  ⊞-ne-hom : ∀ {n i j}
           → (c : ℕ.Ordering i j)
           → (x : Coeff n)
           → (xs : Coeffs n)
           → (y : Coeff n)
           → (ys : Coeffs n)
           → (ρ : Carrier)
           → (Ρ : Vec Carrier n)
           → ⟦ ⊞-ne c x xs y ys ⟧ (ρ ∷ Ρ)
           ≈ ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
  ⊞-ne-hom (ℕ.equal i) x xs y ys ρ Ρ =
    let x′  = ⟦ proj₁~ x ⟧ Ρ
        y′  = ⟦ proj₁~ y ⟧ Ρ
        xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
        ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
    in
    begin
      ⟦ (proj₁~ x ⊞ proj₁~ y , i) ∷↓ xs ⊞ ys ⟧ (ρ ∷ Ρ)
    ≈⟨ ∷↓-hom _ i (xs ⊞ ys) ρ Ρ ⟩
      (⟦ proj₁~ x ⊞ proj₁~ y ⟧ Ρ + ⟦ xs ⊞ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
    ≈⟨ ≪* begin
            ⟦ proj₁~ x ⊞ proj₁~ y ⟧ Ρ + ⟦ xs ⊞ ys ⟧ (ρ ∷ Ρ) * ρ
          ≈⟨ ⊞-hom (proj₁~ x) (proj₁~ y) Ρ ⟨ +-cong ⟩ (≪* ⊞-coeffs-hom xs ys ρ Ρ) ⟩
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
  ⊞-ne-hom (ℕ.less i k) x xs y ys ρ Ρ = ⊞-ne-r-step-hom i k y ys x xs ρ Ρ ︔ +-comm _ _
  ⊞-ne-hom (ℕ.greater j k) = ⊞-ne-r-step-hom j k

  ⊞-ne-r-step-hom : ∀ {n} j k
                  → (x : Coeff n)
                  → (xs : Coeffs n)
                  → (y : Coeff n)
                  → (ys : Coeffs n)
                  → (ρ : Carrier)
                  → (Ρ : Vec Carrier n)
                  → ⟦ (y , j) ∷ ⊞-ne-r k x xs ys ⟧ (ρ ∷ Ρ)
                  ≈ ⟦ (x , suc (j ℕ.+ k)) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
  ⊞-ne-r-step-hom j k x xs y ys ρ Ρ =
    let x′  = ⟦ proj₁~ x ⟧ Ρ
        y′  = ⟦ proj₁~ y ⟧ Ρ
        xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
        ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
    in
    begin
      (y′ + ⟦ ⊞-ne-r k x xs ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j
    ≈⟨ ≪* +≫ ≪* ⊞-ne-r-hom k x xs ys ρ Ρ ⟩
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
    ≡⟨⟩
      ⟦ (x , suc (j ℕ.+ k)) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
    ∎

  ⊞-ne-r-hom : ∀ {n} i
             → (x : Coeff n)
             → (xs : Coeffs n)
             → (ys : Coeffs n)
             → (ρ : Carrier)
             → (Ρ : Vec Carrier n)
             → ⟦ ⊞-ne-r i x xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ ys ⟧ (ρ ∷ Ρ)
  ⊞-ne-r-hom i x xs [] ρ Ρ = sym (+-identityʳ _)
  ⊞-ne-r-hom i x xs ((y , j) ∷ ys) = ⊞-ne-hom (ℕ.compare i j) x xs y ys

mutual
  ⊟-hom : ∀ {n}
        → (xs : Poly n)
        → (Ρ : Vec Carrier n)
        → ⟦ ⊟ xs ⟧ Ρ ≈ - ⟦ xs ⟧ Ρ
  ⊟-hom {ℕ.zero} xs [] = -‿homo _
  ⊟-hom {suc _} xs (ρ ∷ Ρ) = ⊟-hom-coeffs xs ρ Ρ

  ⊟-hom-coeffs : ∀ {n}
              → (xs : Coeffs n)
              → (ρ : Carrier)
              → (Ρ : Vec Carrier n)
              → ⟦ ⊟ xs ⟧ (ρ ∷ Ρ) ≈ - ⟦ xs ⟧ (ρ ∷ Ρ)
  ⊟-hom-coeffs [] ρ Ρ =
    begin
      ⟦ ⊟ [] ⟧ (ρ ∷ Ρ)
    ≡⟨⟩
      0#
    ≈⟨ sym (zeroʳ _) ⟩
      - 0# * 0#
    ≈⟨ -‿*-distribˡ 0# 0# ⟩
      - (0# * 0#)
    ≈⟨ -‿cong (zeroˡ 0#) ⟩
      - 0#
    ≡⟨⟩
      - ⟦ [] ⟧ (ρ ∷ Ρ)
    ∎
  ⊟-hom-coeffs  ((x ,~ x≠0 , i) ∷ xs) ρ Ρ =
    begin
      ⟦ ⊟ ((x ,~ x≠0 , i) ∷ xs) ⟧ (ρ ∷ Ρ)
    ≡⟨⟩
      ⟦ (⊟ x , i) ∷↓ ⊟ xs ⟧ (ρ ∷ Ρ)
    ≈⟨ ∷↓-hom (⊟ x) i (⊟ xs) ρ Ρ ⟩
      (⟦ ⊟ x ⟧ Ρ + ⟦ ⊟ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
    ≈⟨ ≪* (⊟-hom x Ρ ⟨ +-cong ⟩ (≪* ⊟-hom-coeffs xs ρ Ρ)) ⟩
      (- ⟦ x ⟧ Ρ + - ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
    ≈⟨ ≪* +≫ -‿*-distribˡ _ ρ ⟩
      (- ⟦ x ⟧ Ρ + - (⟦ xs ⟧ (ρ ∷ Ρ) * ρ)) * ρ ^ i
    ≈⟨ ≪* -‿+-comm _ _ ⟩
      - (⟦ x ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
    ≈⟨ -‿*-distribˡ _ _ ⟩
      - ⟦ (x ,~ x≠0 , i) ∷ xs ⟧ (ρ ∷ Ρ)
    ∎

mutual
  ⋊-hom : ∀ {n}
        → (x : Poly n)
        → (ys : Poly (suc n))
        → (ρ : Carrier)
        → (Ρ : Vec Carrier n)
        → ⟦ x ⋊ ys ⟧ (ρ ∷ Ρ) ≈ ⟦ x ⟧ Ρ * ⟦ ys ⟧ (ρ ∷ Ρ)
  ⋊-hom x [] ρ Ρ = sym (zeroʳ (⟦ x ⟧ Ρ))
  ⋊-hom x ((y , j) ∷ ys) ρ Ρ =
    let x′  = ⟦ x ⟧ Ρ
        y′  = ⟦ proj₁~ y ⟧ Ρ
        ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
    in
    begin
      ⟦ x ⋊ ((y , j) ∷ ys) ⟧ (ρ ∷ Ρ)
    ≡⟨⟩
      ⟦ (x ⊠ proj₁~ y , j) ∷↓ x ⋊ ys ⟧ (ρ ∷ Ρ)
    ≈⟨ ∷↓-hom _ j (x ⋊ ys) ρ Ρ ⟩
      (⟦ x ⊠ proj₁~ y ⟧ Ρ + ⟦ x ⋊ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j
    ≈⟨ ≪* (⊠-hom x _ Ρ ⟨ +-cong ⟩ (≪* ⋊-hom x ys ρ Ρ ︔ *-assoc _ _ _))⟩
      (x′ * y′ + x′ * (ys′ * ρ)) * ρ ^ j
    ≈⟨ ≪* sym (distribˡ x′ _ _ ) ⟩
      x′ * (y′ + ys′ * ρ) * ρ ^ j
    ≈⟨ *-assoc _ _ _ ⟩
      x′ * ((y′ + ys′ * ρ) * ρ ^ j)
    ∎

  ⊠-hom : ∀ {n}
        → (xs : Poly n)
        → (ys : Poly n)
        → (Ρ : Vec Carrier n)
        → ⟦ xs ⊠ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ * ⟦ ys ⟧ Ρ
  ⊠-hom {ℕ.zero} xs ys [] = *-homo _ _
  ⊠-hom {suc n} xs ys (ρ ∷ Ρ) = ⊠-coeffs-hom xs ys ρ Ρ

  ⊠-step-hom : ∀ {n}
             → (x : Poly n)
             → (xs : Coeffs n)
             → (y : Poly n)
             → (ys : Coeffs n)
             → (ρ : Carrier)
             → (Ρ : Vec Carrier n)
             → ⟦ x ⊠ y ⟧ Ρ + ⟦ x ⋊ ys ⊞ ⊠-shift y ys xs ⟧ (ρ ∷ Ρ) * ρ
             ≈ (⟦ x ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * (⟦ y ⟧ Ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
  ⊠-step-hom x xs y ys ρ Ρ =
    let y′  = ⟦ y ⟧ Ρ
        x′  = ⟦ x ⟧ Ρ
        ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
        xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
    in
    begin
      ⟦ x ⊠ y ⟧ Ρ + ⟦ x ⋊ ys ⊞ ⊠-shift y ys xs ⟧ (ρ ∷ Ρ) * ρ
    ≈⟨ ⊠-hom x y Ρ ⟨ +-cong ⟩ (≪* ⊞-hom (x ⋊ ys) _ (ρ ∷ Ρ)) ⟩
      x′ * y′ + (⟦ x ⋊ ys ⟧ (ρ ∷ Ρ) + ⟦ ⊠-shift y ys xs ⟧ (ρ ∷ Ρ)) * ρ
    ≈⟨ +≫ ≪* (⋊-hom x ys ρ Ρ ⟨ +-cong ⟩ ⊠-shift-hom y ys xs ρ Ρ) ⟩
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

  ⊠-shift-hom : ∀ {n}
             → (y : Poly n)
             → (ys : Coeffs n)
             → (xs : Coeffs n)
             → (ρ : Carrier)
             → (Ρ : Vec Carrier n)
             → ⟦ ⊠-shift y ys xs ⟧ (ρ ∷ Ρ)
             ≈ ⟦ xs ⟧ (ρ ∷ Ρ) * (⟦ y ⟧ Ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
  ⊠-shift-hom y ys [] ρ Ρ = sym (zeroˡ _)
  ⊠-shift-hom y ys ((x ,~ x≠0 , i) ∷ xs) ρ Ρ =
    let y′ = ⟦ y ⟧ Ρ
        x′ = ⟦ x ⟧ Ρ
        ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
        xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
    in
    begin
      ⟦ (x ⊠ y , i) ∷↓ x ⋊ ys ⊞ ⊠-shift y ys xs ⟧ (ρ ∷ Ρ)
    ≈⟨ ∷↓-hom _ _ _ ρ Ρ ⟩
      (⟦ x ⊠ y ⟧ Ρ + ⟦ x ⋊ ys ⊞ ⊠-shift y ys xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
    ≈⟨ ≪* ⊠-step-hom x xs y ys ρ Ρ ⟩
      (x′ + xs′ * ρ) * (y′ + ys′ * ρ) * ρ ^ i
    ≈⟨ *-assoc _ _ _ ︔ *≫ *-comm _ _ ︔ sym (*-assoc _ _ _) ⟩
      (x′ + xs′ * ρ) * ρ ^ i * (y′ + ys′ * ρ)
    ≡⟨⟩
      ⟦ (x ,~ x≠0 , i) ∷ xs ⟧ (ρ ∷ Ρ) * (⟦ y ⟧ Ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
    ∎

  ⊠-coeffs-hom : ∀ {n}
               → (xs : Coeffs n)
               → (ys : Coeffs n)
               → (ρ : Carrier)
               → (Ρ : Vec Carrier n)
               → ⟦ ⊠-coeffs xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ ys ⟧ (ρ ∷ Ρ)
  ⊠-coeffs-hom [] ys ρ Ρ = sym (zeroˡ _)
  ⊠-coeffs-hom (x ∷ xs) [] ρ Ρ = sym (zeroʳ _)
  ⊠-coeffs-hom ((x , i) ∷ xs) ((y , j) ∷ ys) ρ Ρ =
    let x′ = ⟦ proj₁~ x ⟧ Ρ
        y′ = ⟦ proj₁~ y ⟧ Ρ
        xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
        ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
    in
    begin
      ⟦ ⊠-coeffs ((x , i) ∷ xs) ((y , j) ∷ ys) ⟧ (ρ ∷ Ρ)
    ≡⟨⟩
      ⟦ (proj₁~ x ⊠ proj₁~ y , j ℕ.+ i) ∷↓ proj₁~ x ⋊ ys ⊞ ⊠-shift (proj₁~ y) ys xs ⟧ (ρ ∷ Ρ)
    ≈⟨ ∷↓-hom _ _ _ ρ Ρ ⟩
      (⟦ proj₁~ x ⊠ proj₁~ y ⟧ Ρ + ⟦ proj₁~ x ⋊ ys ⊞ ⊠-shift (proj₁~ y) ys xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ (j ℕ.+ i)
    ≈⟨ ≪* ⊠-step-hom (proj₁~ x) xs (proj₁~ y) ys ρ Ρ ⟩
      (x′ + xs′ * ρ) * (y′ + ys′ * ρ) * ρ ^ (j ℕ.+ i)
    ≈⟨ *≫ sym (pow-add ρ j i) ⟩
      (x′ + xs′ * ρ) * (y′ + ys′ * ρ) * (ρ ^ j * ρ ^ i)
    ≈⟨ *-assoc _ _ _ ⟩
      (x′ + xs′ * ρ) * ((y′ + ys′ * ρ) * (ρ ^ j * ρ ^ i))
    ≈⟨ *≫ sym (*-assoc _ _ _) ⟩
      (x′ + xs′ * ρ) * (((y′ + ys′ * ρ) * ρ ^ j) * ρ ^ i)
    ≈⟨ *≫ *-comm _ _ ⟩
      (x′ + xs′ * ρ) * (ρ ^ i * ((y′ + ys′ * ρ) * ρ ^ j))
    ≈⟨ sym (*-assoc _ _ _) ⟩
      ((x′ + xs′ * ρ) * ρ ^ i) * ((y′ + ys′ * ρ) * ρ ^ j)
    ≡⟨⟩
      ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) * ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
    ∎

κ-hom : ∀ {n}
      → (x : Raw.Carrier)
      → (Ρ : Vec Carrier n)
      → ⟦ κ x ⟧ Ρ ≈ ⟦ x ⟧ᵣ
κ-hom x [] = refl
κ-hom x (ρ ∷ Ρ) =
  begin
    ⟦ κ x ⟧ (ρ ∷ Ρ)
  ≈⟨ ∷↓-hom _ _ _ ρ Ρ ⟩
    (⟦ κ x ⟧ Ρ + 0# * ρ) * ρ ^ 0
  ≈⟨ *-identityʳ _ ⟩
    ⟦ κ x ⟧ Ρ + 0# * ρ
  ≈⟨ κ-hom x Ρ ⟨ +-cong ⟩ zeroˡ ρ ⟩
    ⟦ x ⟧ᵣ + 0#
  ≈⟨ +-identityʳ _ ⟩
    ⟦ x ⟧ᵣ
  ∎

ι-hom : ∀ {n} → (x : Fin n) → (Ρ : Vec Carrier n) → ⟦ ι x ⟧ Ρ ≈ Vec.lookup x Ρ
ι-hom Fin.zero (ρ ∷ Ρ) =
  begin
    ⟦ (κ Raw.1# , 1) ∷↓ [] ⟧ (ρ ∷ Ρ)
  ≈⟨ ∷↓-hom _ _ _ ρ Ρ ⟩
    (⟦ κ Raw.1# ⟧ Ρ + 0# * ρ) * ρ ^ 1
  ≈⟨ ((κ-hom Raw.1# Ρ ⟨ +-cong ⟩ zeroˡ ρ) ︔ +-identityʳ _) ⟨ *-cong ⟩ *-identityʳ ρ ⟩
    ⟦ Raw.1# ⟧ᵣ * ρ
  ≈⟨ ≪* 1-homo ︔ *-identityˡ ρ ⟩
    ρ
  ∎
ι-hom (Fin.suc x) (ρ ∷ Ρ) =
  begin
    ⟦ (ι x , 0) ∷↓ [] ⟧ (ρ ∷ Ρ)
  ≈⟨ ∷↓-hom _ _ _ ρ Ρ ⟩
    (⟦ ι x ⟧ Ρ + 0# * ρ) * ρ ^ 0
  ≈⟨ *-identityʳ _ ⟩
    ⟦ ι x ⟧ Ρ + 0# * ρ
  ≈⟨ ι-hom x Ρ ⟨ +-cong ⟩ zeroˡ ρ ⟩
    Vec.lookup x Ρ + 0#
  ≈⟨ +-identityʳ _ ⟩
    Vec.lookup x Ρ
  ∎

