{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters

module Polynomial.Homomorphism.Exponentiation
  {r₁ r₂ r₃}
  (homo : Homomorphism r₁ r₂ r₃)
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
open import Polynomial.Homomorphism.Semantics homo
open import Polynomial.Homomorphism.Multiplication homo

open import Polynomial.Exponentiation rawRing

⊡-mult-hom : ∀ {n} → (i : ℕ) → (xs : Poly n) → ∀ ρ → ⟦ ⊡-mult i xs ⟧ ρ ≈ ⟦ xs ⟧ ρ ^ i
⊡-mult-hom ℕ.zero xs ρ = κ-hom Raw.1# ρ ⟨ trans ⟩ 1-homo
⊡-mult-hom (suc i) xs ρ = ⊠-hom xs (⊡-mult i xs) ρ ⟨ trans ⟩ (*≫ ⊡-mult-hom i xs ρ)

⊡-hom : ∀ {n} → (xs : Poly n) → (i : ℕ) → ∀ ρ → ⟦ xs ⊡ i ⟧ ρ ≈ ⟦ xs ⟧ ρ ^ i
⊡-hom xs@(Κ _ Π _) i = ⊡-mult-hom i xs
⊡-hom xs@(Σ [] Π _) i = ⊡-mult-hom i xs
⊡-hom xs@(Σ (_ ∷ _ ∷ _) Π _) i = ⊡-mult-hom i xs
⊡-hom xs@(Σ (x ≠0 Δ j ∷ []) Π i≤n) i ρ =
  let (ρ′ , Ρ) = drop-1 i≤n ρ
  in
  begin
    ⟦ x ⊡ i Δ (i ℕ.* j) ∷↓ [] Π↓ i≤n ⟧ ρ
  ≈⟨ Π↓-hom (x ⊡ i Δ (i ℕ.* j) ∷↓ []) i≤n ρ ⟩
    Σ⟦ x ⊡ i Δ (i ℕ.* j) ∷↓ [] ⟧ (drop-1 i≤n ρ)
  ≈⟨ ∷↓-hom (x ⊡ i) (i ℕ.* j) [] ρ′ Ρ ⟩
    (⟦ x ⊡ i ⟧ Ρ + 0# * ρ′) * ρ′ ^ (i ℕ.* j)
  ≈⟨ ≪* ((+≫ zeroˡ _) ⟨ trans ⟩ +-identityʳ _) ⟩
    (⟦ x ⊡ i ⟧ Ρ) * ρ′ ^ (i ℕ.* j)
  ≈⟨ ≪* ⊡-hom x i Ρ ⟩
    (⟦ x ⟧ Ρ ^ i) * ρ′ ^ (i ℕ.* j)
  ≈⟨ *≫ sym (pow-mult ρ′ j i ) ⟩
    (⟦ x ⟧ Ρ ^ i) * (ρ′ ^ j) ^ i
  ≈⟨ sym (pow-distrib _ _ i) ⟩
    (⟦ x ⟧ Ρ * ρ′ ^ j) ^ i
  ≈⟨ pow-cong i (≪* sym ((+≫ zeroˡ _) ⟨ trans ⟩ +-identityʳ _)) ⟩
    ((⟦ x ⟧ Ρ + 0# * ρ′) * ρ′ ^ j) ^ i
  ∎
