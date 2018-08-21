{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Ring.Homomorphism.Semantics
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

κ-hom : ∀ {n}
      → (x : Raw.Carrier)
      → (Ρ : Vec Carrier n)
      → ⟦ κ x ⟧ Ρ ≈ ⟦ x ⟧ᵣ
κ-hom x _ = refl

ι-hom : ∀ {n} → (i : Fin n) → (Ρ : Vec Carrier n) → ⟦ ι i ⟧ Ρ ≈ Vec.lookup i Ρ
ι-hom i Ρ′ =
  let (ρ , Ρ) = drop-1 (Fin⇒≤ i) Ρ′
  in
  begin
    ⟦ (κ Raw.1# ^ 1 ∷↓ []) Π↓ Fin⇒≤ i ⟧ Ρ′
  ≈⟨ Π↓-hom (κ Raw.1# ^ 1 ∷↓ []) (Fin⇒≤ i) Ρ′ ⟩
    Σ⟦ κ Raw.1# ^ 1 ∷↓ [] ⟧ (ρ , Ρ)
  ≈⟨ ∷↓-hom (κ Raw.1#) 1 [] ρ Ρ  ⟩
    (⟦ κ Raw.1# ⟧ Ρ + Σ⟦ [] ⟧ (ρ , Ρ) * ρ) * ρ ^ 1
  ≡⟨⟩
    (⟦ Raw.1# ⟧ᵣ + 0# * ρ) * (ρ * 1#)
  ≈⟨ 1-homo ⟨ +-cong ⟩ zeroˡ ρ ⟨ *-cong ⟩ *-identityʳ ρ ⟩
    (1# + 0#) * ρ
  ≈⟨ ≪* +-identityʳ _ ⟩
    1# * ρ
  ≈⟨ *-identityˡ ρ ⟩
    ρ
  ≡⟨ drop-1⇒lookup i Ρ′ ⟩
    Vec.lookup i Ρ′
  ∎
