{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
open import Relation.Binary

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.CommutativeSemiring.Homomorphism
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring
open import Polynomials.CommutativeSemiring.Reasoning commutativeSemiring
open import Polynomials.CommutativeSemiring.Normal commutativeSemiring _≟C_

open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product
import Data.Nat.Properties as ℕ-≡
import Relation.Binary.PropositionalEquality as ≡
open import Function
open import Data.List as List using (_∷_; [])
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Polynomials.Irrelevant.Product
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
zero-hom {zero} (lift p) p=0 [] = p=0
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
  ⊞-hom {ℕ.zero} xs ys [] = refl
  ⊞-hom {suc n} xs ys (ρ ∷ Ρ) = ⊞-coeffs-hom xs ys ρ Ρ

  ⊞-coeffs-hom : ∀ {n}
              → (xs : Coeffs n)
              → (ys : Coeffs n)
              → (ρ : Carrier)
              → (Ρ : Vec Carrier n)
              → ⟦ ⊞-coeffs xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ xs ⟧ (ρ ∷ Ρ) + ⟦ ys ⟧ (ρ ∷ Ρ)
  ⊞-coeffs-hom [] ys ρ Ρ = sym (+-identityˡ (⟦ ys ⟧ (ρ ∷ Ρ)))
  ⊞-coeffs-hom (x ∷ xs) [] ρ Ρ = sym (+-identityʳ (⟦ x ∷ xs ⟧ (ρ ∷ Ρ)))
  ⊞-coeffs-hom ((x , i) ∷ xs) ((y , j) ∷ ys) ρ Ρ = ⊞-ne-hom (ℕ.compare i j) x xs y ys ρ Ρ

  ⊞-ne-hom : ∀ {n i j}
          → (c : ℕ.Ordering i j)
          → (x : Coeff n)
          → (xs : Coeffs n)
          → (y : Coeff n)
          → (ys : Coeffs n)
          → (ρ : Carrier)
          → (Ρ : Vec Carrier n)
          → ⟦ ⊞-ne c x xs y ys ⟧ (ρ ∷ Ρ) ≈ ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
  ⊞-ne-hom (ℕ.equal i) x xs y ys ρ Ρ =
    let x′ = ⟦ fst~ x ⟧ Ρ
        y′ = ⟦ fst~ y ⟧ Ρ
    in
    begin
      ⟦ (fst~ x ⊞ fst~ y , i) ∷↓ xs ⊞ ys ⟧ (ρ ∷ Ρ)
    ≈⟨ (∷↓-hom _ i (xs ⊞ ys) ρ Ρ) ⟩
      (⟦ fst~ x ⊞ fst~ y ⟧ Ρ + ⟦ xs ⊞ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
    ≈⟨ ≪* begin
            ⟦ fst~ x ⊞ fst~ y ⟧ Ρ + ⟦ xs ⊞ ys ⟧ (ρ ∷ Ρ) * ρ
          ≈⟨ ⊞-hom (fst~ x) (fst~ y) Ρ ⟨ +-cong ⟩ (≪* ⊞-coeffs-hom xs ys ρ Ρ) ⟩
            (x′ + y′) + (⟦ xs ⟧ (ρ ∷ Ρ) + ⟦ ys ⟧ (ρ ∷ Ρ)) * ρ
          ≈⟨ +≫ distribʳ ρ _ _ ⟩
            (x′ + y′) + (⟦ xs ⟧ (ρ ∷ Ρ) * ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
          ≈⟨ +-assoc x′ y′ _ ⟩
            x′ + (y′ + (⟦ xs ⟧ (ρ ∷ Ρ) * ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ))
          ≈⟨ +≫ sym ( +-assoc y′ _ _ ) ⟩
            x′ + ((y′ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
          ≈⟨ +≫ ≪+ +-comm y′ _ ⟩
            x′ + ((⟦ xs ⟧ (ρ ∷ Ρ) * ρ + y′) + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
          ≈⟨ +≫ +-assoc _ y′ _ ⟩
            x′ + (⟦ xs ⟧ (ρ ∷ Ρ) * ρ + (y′ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ))
          ≈⟨ sym (+-assoc x′ _ _) ⟩
            (x′ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) + (⟦ fst~ y ⟧ Ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
          ∎
    ⟩
      ((x′ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) + (y′ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)) * ρ ^ i
    ≈⟨ distribʳ (ρ ^ i) _ _ ⟩
      (x′ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i + (y′ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
    ∎
  ⊞-ne-hom (ℕ.less i k) x xs y ys ρ Ρ =
    let x′ = ⟦ fst~ x ⟧ Ρ
    in
    begin
      (x′ + ⟦ ⊞-ne-l k xs y ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
    ≈⟨ ≪* +≫ ≪* ⊞-ne-l-hom k xs y ys ρ Ρ ⟩
      (x′ + (⟦ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , k) ∷ ys ⟧ (ρ ∷ Ρ)) * ρ) * ρ ^ i
    ≈⟨ ≪* +≫ distribʳ ρ _ _ ⟩
      (x′ + (⟦ xs ⟧ (ρ ∷ Ρ) * ρ + ⟦ (y , k) ∷ ys ⟧ (ρ ∷ Ρ) * ρ)) * ρ ^ i
    ≈⟨ ≪* sym (+-assoc x′ _ _) ⟩
      (x′ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ + ⟦ (y , k) ∷ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
    ≈⟨ distribʳ (ρ ^ i) _ _ ⟩
      ⟦ (x , i)  ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , k) ∷ ys ⟧ (ρ ∷ Ρ) * ρ * ρ ^ i
    ≈⟨ +≫ (*-assoc _ ρ (ρ ^ i) ︔ *-assoc _ (ρ ^ k) (ρ ^ suc i) ︔ *≫ pow-add _ k (suc i))⟩
      ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y  , k ℕ.+ suc i) ∷ ys ⟧ (ρ ∷ Ρ)
    ≡⟨ ≡.cong (λ ik → ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , ik) ∷ ys ⟧ (ρ ∷ Ρ)) (ℕ-≡.+-comm k (suc i)) ⟩
      ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , suc (i ℕ.+ k)) ∷ ys ⟧ (ρ ∷ Ρ)
    ∎
  ⊞-ne-hom (ℕ.greater j k) x xs y ys ρ Ρ =
    let y′ = ⟦ fst~ y ⟧ Ρ
    in
    begin
      (y′ + ⟦ ⊞-ne-r k x xs ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j
    ≈⟨ ≪* +≫ ≪* (⊞-ne-r-hom k x xs ys ρ Ρ ︔ +-comm _ _) ⟩
      (y′ + (⟦ ys ⟧ (ρ ∷ Ρ) + ⟦ (x , k) ∷ xs ⟧ (ρ ∷ Ρ)) * ρ) * ρ ^ j
    ≈⟨ ≪* +≫ distribʳ ρ _ _ ⟩
      (y′ + (⟦ ys ⟧ (ρ ∷ Ρ) * ρ + ⟦ (x , k) ∷ xs ⟧ (ρ ∷ Ρ) * ρ)) * ρ ^ j
    ≈⟨ ≪* sym (+-assoc _ _ _) ⟩
      (y′ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ + ⟦ (x , k) ∷ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j
    ≈⟨ distribʳ (ρ ^ j) _ _ ⟩
      ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ) + (⟦ (x , k) ∷ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j
    ≈⟨ +≫ *-assoc _ ρ _ ⟩
      ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ) + ⟦ (x , k) ∷ xs ⟧ (ρ ∷ Ρ) * ρ ^ suc j
    ≈⟨ +≫ (*-assoc _ _ _ ︔ *≫ pow-add _ k (suc j)) ⟩
      ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ) + ⟦ (x , k ℕ.+ suc j) ∷ xs ⟧ (ρ ∷ Ρ)
    ≈⟨ +-comm _ _ ⟩
      ⟦ (x , k ℕ.+ suc j) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
    ≡⟨ ≡.cong (λ kj → ⟦ (x , kj) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)) (ℕ-≡.+-comm k (suc j)) ⟩
      ⟦ (x , suc (j ℕ.+ k)) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
    ∎

  ⊞-ne-l-hom : ∀ {n} k
            → (xs : Coeffs n)
            → (y : Coeff n)
            → (ys : Coeffs n)
            → (ρ : Carrier)
            → (Ρ : Vec Carrier n)
            → ⟦ ⊞-ne-l k xs y ys ⟧ (ρ ∷ Ρ) ≈ ⟦ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , k) ∷ ys ⟧ (ρ ∷ Ρ)
  ⊞-ne-l-hom k [] y ys ρ Ρ = sym (+-identityˡ _)
  ⊞-ne-l-hom k ((x , i) ∷ xs) y ys ρ Ρ = ⊞-ne-hom (ℕ.compare i k) x xs y ys ρ Ρ

  ⊞-ne-r-hom : ∀ {n} k
            → (x : Coeff n)
            → (xs : Coeffs n)
            → (ys : Coeffs n)
            → (ρ : Carrier)
            → (Ρ : Vec Carrier n)
            → ⟦ ⊞-ne-r k x xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ (x , k) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ ys ⟧ (ρ ∷ Ρ)
  ⊞-ne-r-hom k x xs [] ρ Ρ = sym (+-identityʳ _)
  ⊞-ne-r-hom k x xs ((y , j) ∷ ys) ρ Ρ = ⊞-ne-hom (ℕ.compare k j) x xs y ys ρ Ρ

mutual
  ⋊-hom : ∀ {n}
        → (x : Poly n)
        → (ys : Poly (suc n))
        → (ρ : Carrier)
        → (Ρ : Vec Carrier n)
        → ⟦ x ⋊ ys ⟧ (ρ ∷ Ρ) ≈ ⟦ x ⟧ Ρ * ⟦ ys ⟧ (ρ ∷ Ρ)
  ⋊-hom x [] ρ Ρ = sym (zeroʳ (⟦ x ⟧ Ρ))
  ⋊-hom x ((y , j) ∷ ys) ρ Ρ =
    begin
      ⟦ x ⋊ ((y , j) ∷ ys) ⟧ (ρ ∷ Ρ)
    ≡⟨⟩
      ⟦ (x ⊠ fst~ y , j) ∷↓ x ⋊ ys ⟧ (ρ ∷ Ρ)
    ≈⟨ ∷↓-hom _ j (x ⋊ ys) ρ Ρ ⟩
      (⟦ x ⊠ fst~ y ⟧ Ρ + ⟦ x ⋊ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j
    ≈⟨ ≪* +≫ ≪* ⋊-hom x ys ρ Ρ ⟩
      (⟦ x ⊠ fst~ y ⟧ Ρ + ⟦ x ⟧ Ρ * ⟦ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j
    ≈⟨ ≪* +≫ *-assoc _ _ _ ⟩
      (⟦ x ⊠ fst~ y ⟧ Ρ + ⟦ x ⟧ Ρ * (⟦ ys ⟧ (ρ ∷ Ρ) * ρ)) * ρ ^ j
    ≈⟨ ≪* ≪+ ⊠-hom x (fst~ y) Ρ ⟩
      (⟦ x ⟧ Ρ * ⟦ fst~ y ⟧ Ρ + ⟦ x ⟧ Ρ * (⟦ ys ⟧ (ρ ∷ Ρ) * ρ)) * ρ ^ j
    ≈⟨ ≪* sym (distribˡ (⟦ x ⟧ Ρ) _ _) ⟩
      ⟦ x ⟧ Ρ * (⟦ fst~ y ⟧ Ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j
    ≈⟨ *-assoc _ _ _ ⟩
      ⟦ x ⟧ Ρ * ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
    ∎

  ⊠-hom : ∀ {n}
        → (xs : Poly n)
        → (ys : Poly n)
        → (Ρ : Vec Carrier n)
        → ⟦ xs ⊠ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ * ⟦ ys ⟧ Ρ
  ⊠-hom {ℕ.zero} xs ys [] = refl
  ⊠-hom {suc n} xs ys (ρ ∷ Ρ) = ⊠-coeffs-hom xs ys ρ Ρ

  ⊠-coeffs-hom : ∀ {n}
               → (xs : Coeffs n)
               → (ys : Coeffs n)
               → (ρ : Carrier)
               → (Ρ : Vec Carrier n)
               → ⟦ ⊠-coeffs xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ ys ⟧ (ρ ∷ Ρ)
  ⊠-coeffs-hom [] ys ρ Ρ = sym (zeroˡ _)
  ⊠-coeffs-hom (x ∷ xs) [] ρ Ρ = sym (zeroʳ _)
  ⊠-coeffs-hom ((x , i) ∷ xs) ((y , j) ∷ ys) ρ Ρ =
    let x′ = ⟦ fst~ x ⟧ Ρ
        y′ = ⟦ fst~ y ⟧ Ρ
    in
    begin
      ⟦ ⊠-coeffs ((x , i) ∷ xs) ((y , j) ∷ ys) ⟧ (ρ ∷ Ρ)
    ≡⟨⟩
      ⟦ (fst~ x ⊠ fst~ y , j ℕ.+ i) ∷↓ fst~ x ⋊ ys ⊞ xs ⊠ ((y , 0) ∷ ys) ⟧ (ρ ∷ Ρ)
    ≈⟨ ∷↓-hom _ _ _ ρ Ρ ⟩
      (⟦ fst~ x ⊠ fst~ y ⟧ Ρ + ⟦ fst~ x ⋊ ys ⊞ xs ⊠ ((y , 0) ∷ ys) ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ (j ℕ.+ i)
    ≈⟨ ≪* ≪+ ⊠-hom (fst~ x) (fst~ y) Ρ ⟩
      (x′ * y′ + ⟦ fst~ x ⋊ ys ⊞ xs ⊠ ((y , 0) ∷ ys) ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ (j ℕ.+ i)
    ≈⟨ ≪* +≫ ≪* (⊞-hom (fst~ x ⋊ ys) _ (ρ ∷ Ρ)  ︔ (⋊-hom (fst~ x) ys ρ Ρ ⟨ +-cong ⟩ ⊠-coeffs-hom xs _ ρ Ρ)) ⟩
      (x′ * y′ + (x′ * ⟦ ys ⟧ (ρ ∷ Ρ) + ⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ (y , 0) ∷ ys ⟧ (ρ ∷ Ρ)) * ρ) * ρ ^ (j ℕ.+ i)
    ≈⟨ ≪* +≫ distribʳ ρ _ _ ⟩
      (x′ * y′ + (x′ * ⟦ ys ⟧ (ρ ∷ Ρ) * ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ (y , 0) ∷ ys ⟧ (ρ ∷ Ρ) * ρ)) * ρ ^ (j ℕ.+ i)
    ≈⟨ ≪* sym (+-assoc (x′ * y′) _ _) ⟩
      (x′ * y′ + x′ * ⟦ ys ⟧ (ρ ∷ Ρ) * ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ (y , 0) ∷ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ (j ℕ.+ i)
    ≈⟨ ≪* ≪+ (+≫ *-assoc x′ _ ρ ︔ sym (distribˡ x′ _ _)) ⟩
      (x′ * (y′ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ) + ⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ (y , 0) ∷ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ (j ℕ.+ i)
    ≈⟨ *≫ sym (pow-add ρ j i) ⟩
      (x′ * (y′ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ) + ⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ (y , 0) ∷ ys ⟧ (ρ ∷ Ρ) * ρ) * (ρ ^ j * ρ ^ i)
    ≈⟨ sym (*-assoc _ _ _) ⟩
      (x′ * (y′ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ) + ⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ (y , 0) ∷ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j * ρ ^ i
    ≈⟨ ≪* distribʳ (ρ ^ j) _ _ ⟩
      (x′ * (y′ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j + ⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ (y , 0) ∷ ys ⟧ (ρ ∷ Ρ) * ρ * ρ ^ j) * ρ ^ i
    ≈⟨ ≪* ≪+ (*-assoc x′ _ _) ⟩
      (x′ * ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ) + ((⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ (y , 0) ∷ ys ⟧ (ρ ∷ Ρ)) * ρ) * ρ ^ j) * ρ ^ i
    ≈⟨ ≪* +≫ ( ≪* ( *-assoc _ _ ρ ︔ *≫ *-comm _ _ ︔ sym (*-assoc _ _ _) ) ︔ *-assoc _ _ _ ) ⟩
      (x′ * ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ) + (⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * (⟦ (y , 0) ∷ ys ⟧ (ρ ∷ Ρ) * ρ ^ j)) * ρ ^ i
    ≈⟨ ≪* +≫ *≫ (*-assoc _ _ _ ︔ *≫ *-identityˡ (ρ ^ j))⟩
      (x′ * ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ) + (⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)) * ρ ^ i
    ≈⟨ ≪* sym (distribʳ _ x′ _) ⟩
      (x′ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ) * ρ ^ i
    ≈⟨ *-assoc _ _ (ρ ^ i) ︔ *≫ *-comm _ (ρ ^ i) ︔ sym (*-assoc _ _ _) ⟩
      (x′ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i * ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
    ≡⟨⟩
      ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) * ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
    ∎

κ-hom : ∀ {n}
      → (x : Carrier)
      → (Ρ : Vec Carrier n)
      → ⟦ κ x ⟧ Ρ ≈ x
κ-hom x [] = refl
κ-hom x (ρ ∷ Ρ) =
  begin
    ⟦ κ x ⟧ (ρ ∷ Ρ)
  ≈⟨ ∷↓-hom _ _ _ ρ Ρ ⟩
    (⟦ κ x ⟧ Ρ + 0# * ρ) * ρ ^ 0
  ≈⟨ *-identityʳ _ ⟩
    ⟦ κ x ⟧ Ρ + 0# * ρ
  ≈⟨ +≫ zeroˡ ρ ⟩
    ⟦ κ x ⟧ Ρ + 0#
  ≈⟨ +-identityʳ _ ⟩
    ⟦ κ x ⟧ Ρ
  ≈⟨ κ-hom x Ρ ⟩
    x
  ∎

ι-hom : ∀ {n} → (x : Fin n) → (Ρ : Vec Carrier n) → ⟦ ι x ⟧ Ρ ≈ Vec.lookup x Ρ
ι-hom Fin.zero (ρ ∷ Ρ) =
  begin
    ⟦ (κ 1# , 1) ∷↓ [] ⟧ (ρ ∷ Ρ)
  ≈⟨ ∷↓-hom _ _ _ ρ Ρ ⟩
    (⟦ κ 1# ⟧ Ρ + 0# * ρ) * ρ ^ 1
  ≈⟨ ((κ-hom 1# Ρ ⟨ +-cong ⟩ zeroˡ ρ) ︔ +-identityʳ 1#) ⟨ *-cong ⟩ *-identityʳ ρ ⟩
    1# * ρ
  ≈⟨ *-identityˡ ρ ⟩
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

