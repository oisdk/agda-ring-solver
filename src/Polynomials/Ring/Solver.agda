{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

module Polynomials.Ring.Solver
  {r₁ r₂ r₃ r₄}
  (coeff : RawRing r₁)
  (Zero-C : Pred (RawRing.Carrier coeff) r₂)
  (zero-c? : Decidable Zero-C)
  (ring : AlmostCommutativeRing r₃ r₄)
  (morphism : coeff -Raw-AlmostCommutative⟶ ring)
  (Zero-C⟶Zero-R : ∀ x → Zero-C x → AlmostCommutativeRing._≈_ ring (_-Raw-AlmostCommutative⟶_.⟦_⟧ morphism x) (AlmostCommutativeRing.0# ring))
  where

module Raw = RawRing coeff
open AlmostCommutativeRing ring
open import Data.Fin as Fin using (Fin)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec)
open import Polynomials.Ring.Expr public

⟦_⟧ : ∀ {n} → Expr Raw.Carrier n → Vec Carrier n → Carrier
⟦ Κ x ⟧ ρ = _-Raw-AlmostCommutative⟶_.⟦_⟧ morphism x
⟦ Ι x ⟧ ρ = Vec.lookup x ρ
⟦ x ⊕ y ⟧ ρ = ⟦ x ⟧ ρ + ⟦ y ⟧ ρ
⟦ x ⊗ y ⟧ ρ = ⟦ x ⟧ ρ * ⟦ y ⟧ ρ
⟦ ⊝ x ⟧ ρ = - ⟦ x ⟧ ρ

open import Polynomials.Ring.Normal coeff Zero-C zero-c?
  using (Poly; _⊞_; _⊠_; ⊟_; κ; ι)

norm : ∀ {n} → Expr Raw.Carrier n → Poly n
norm (Κ x) = κ x
norm (Ι x) = ι x
norm (x ⊕ y) = norm x ⊞ norm y
norm (x ⊗ y) = norm x ⊠ norm y
norm (⊝ x) = ⊟ norm x

open import Polynomials.Ring.Semantics coeff Zero-C zero-c? ring morphism
  renaming (⟦_⟧ to ⟦_⟧ₚ)

⟦_⇓⟧ : ∀ {n} → Expr Raw.Carrier n → Vec Carrier n → Carrier
⟦ x ⇓⟧ = ⟦ norm x ⟧ₚ

import Polynomials.Ring.Homomorphism coeff Zero-C zero-c? ring morphism Zero-C⟶Zero-R
  as Hom
open import Function

correct : ∀ {n} (e : Expr Raw.Carrier n) ρ → ⟦ e ⇓⟧ ρ ≈ ⟦ e ⟧ ρ
correct (Κ x) ρ = Hom.κ-hom x ρ
correct (Ι x) ρ = Hom.ι-hom x ρ
correct (x ⊕ y) ρ = Hom.⊞-hom (norm x) (norm y) ρ ⟨ trans ⟩ (correct x ρ ⟨ +-cong ⟩ correct y ρ)
correct (x ⊗ y) ρ = Hom.⊠-hom (norm x) (norm y) ρ ⟨ trans ⟩ (correct x ρ ⟨ *-cong ⟩ correct y ρ)
correct (⊝ x) ρ = Hom.⊟-hom (norm x) ρ ⟨ trans ⟩ -‿cong (correct x ρ)

open import Relation.Binary.Reflection setoid Ι ⟦_⟧ ⟦_⇓⟧ correct public
