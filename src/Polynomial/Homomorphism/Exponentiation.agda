{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters

module Polynomial.Homomorphism.Exponentiation
  {r₁ r₂ r₃}
  (homo : Homomorphism r₁ r₂ r₃)
  where

open import Function

open import Data.Nat as ℕ using (ℕ; suc; zero; compare)
open import Data.Product  using (_,_; _×_; proj₁; proj₂)
open import Data.List     using (_∷_; [])
open import Data.Vec      using (Vec)

import Data.Nat.Properties as ℕ-Prop
import Relation.Binary.PropositionalEquality as ≡
import Relation.Binary.PropositionalEquality.TrustMe as TrustMe

open Homomorphism homo
open import Polynomial.Homomorphism.Lemmas homo
open import Polynomial.NormalForm homo
open import Polynomial.Reasoning ring
open import Polynomial.Homomorphism.Semantics homo
open import Polynomial.Homomorphism.Multiplication homo

import Polynomial.Exponentiation
module RawPow = Polynomial.Exponentiation rawRing
module CoPow = Polynomial.Exponentiation (RawCoeff.coeffs coeffs)

pow-eval-hom : ∀ x i → ⟦ x CoPow.^ i +1 ⟧ᵣ ≈ ⟦ x ⟧ᵣ RawPow.^ i +1
pow-eval-hom x ℕ.zero = refl
pow-eval-hom x (suc i) = (*-homo _ x) ⟨ trans ⟩ (≪* pow-eval-hom x i)

⊡-mult-hom : ∀ {n} i (xs : Poly n) ρ → ⟦ ⊡-mult i xs ⟧ ρ ≈ ⟦ xs ⟧ ρ RawPow.^ i +1
⊡-mult-hom ℕ.zero xs ρ = refl
⊡-mult-hom (suc i) xs ρ =  ⊠-hom (⊡-mult i xs) xs ρ ⟨ trans ⟩ (≪* ⊡-mult-hom i xs ρ)

⊡-+1-hom : ∀ {n} → (xs : Poly n) → (i : ℕ) → ∀ ρ → ⟦ xs ⊡ i +1 ⟧ ρ ≈ ⟦ xs ⟧ ρ RawPow.^ i +1
⊡-+1-hom (Κ x  Π i≤n) i ρ = pow-eval-hom x i
⊡-+1-hom (Σ [] {()} Π i≤n) i ρ
⊡-+1-hom xs@(Σ (_ ∷ _ ∷ _) Π i≤n) i ρ = ⊡-mult-hom i xs ρ
⊡-+1-hom (Σ (x ≠0 Δ j ∷ []) Π i≤n) i ρ =
  begin
    ⟦ x ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ [] Π↓ i≤n ⟧ ρ
  ≈⟨ Π↓-hom (x ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ []) i≤n ρ ⟩
    Σ⟦ x ⊡ i +1 Δ (j ℕ.+ i ℕ.* j) ∷↓ [] ⟧ (drop-1 i≤n ρ)
  ≈⟨ ∷↓-hom (x ⊡ i +1) (j ℕ.+ i ℕ.* j) [] ρ′ Ρ ⟩
    (ρ′ * 0# + ⟦ x ⊡ i +1 ⟧ Ρ) * (ρ′ RawPow.^ (j ℕ.+ i ℕ.* j))
  ≈⟨ ≪*  (zeroʳ ρ′ ⟨ +-cong ⟩ ⊡-+1-hom x i Ρ ⟨ trans ⟩ +-identityˡ _) ⟩
    (⟦ x ⟧ Ρ RawPow.^ i +1) * (ρ′ RawPow.^ (j ℕ.+ i ℕ.* j))
  ≈⟨ rearrange j ⟩
    ((ρ′ * 0# + ⟦ x ⟧ Ρ) *⟨ ρ′ ⟩^ j) RawPow.^ i +1
  ∎
  where
  ρ′,Ρ = drop-1 i≤n ρ
  ρ′ = proj₁ ρ′,Ρ
  Ρ = proj₂ ρ′,Ρ
  rearrange : ∀ j → (⟦ x ⟧ Ρ RawPow.^ i +1) * (ρ′ RawPow.^ (j ℕ.+ i ℕ.* j)) ≈ ((ρ′ * 0# + ⟦ x ⟧ Ρ) *⟨ ρ′ ⟩^ j) RawPow.^ i +1
  rearrange zero =
    begin
      (⟦ x ⟧ Ρ RawPow.^ i +1) * (ρ′ RawPow.^ (i ℕ.* 0))
    ≡⟨ ≡.cong (λ k → (⟦ x ⟧ Ρ RawPow.^ i +1) * (ρ′ RawPow.^ k)) (ℕ-Prop.*-zeroʳ i) ⟩
      (⟦ x ⟧ Ρ RawPow.^ i +1) * 1#
    ≈⟨ *-identityʳ _ ⟩
      ⟦ x ⟧ Ρ RawPow.^ i +1
    ≈⟨ pow-cong-+1 i (sym ((≪+ zeroʳ _) ⟨ trans ⟩ +-identityˡ _)) ⟩
      (ρ′ * 0# + ⟦ x ⟧ Ρ) RawPow.^ i +1
    ∎
  rearrange j@(suc j′) =
    begin
      (⟦ x ⟧ Ρ RawPow.^ i +1) * (ρ′ RawPow.^ (j ℕ.+ i ℕ.* j))
    ≈⟨ *≫ sym ( pow-mult-+1 ρ′ j′ i) ⟩
      (⟦ x ⟧ Ρ RawPow.^ i +1) * ((ρ′ RawPow.^ j′ +1) RawPow.^ i +1)
    ≈⟨ sym (pow-distrib-+1 (⟦ x ⟧ Ρ) _ i) ⟩
      (⟦ x ⟧ Ρ * (ρ′ RawPow.^ j′ +1)) RawPow.^ i +1
    ≈⟨ pow-cong-+1 i (*-comm _ _ ⟨ trans ⟩ sym (*≫ ((≪+ zeroʳ _) ⟨ trans ⟩ +-identityˡ _))) ⟩
      ((ρ′ * 0# + ⟦ x ⟧ Ρ) *⟨ ρ′ ⟩^ j) RawPow.^ i +1
    ∎

⊡-hom : ∀ {n} → (xs : Poly n) → (i : ℕ) → ∀ ρ → ⟦ xs ⊡ i ⟧ ρ ≈ ⟦ xs ⟧ ρ RawPow.^ i
⊡-hom xs ℕ.zero ρ = 1-homo
⊡-hom xs (suc i) ρ = ⊡-+1-hom xs i ρ
