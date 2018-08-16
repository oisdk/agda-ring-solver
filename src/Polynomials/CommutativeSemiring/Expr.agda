{-# OPTIONS --without-K #-}

open import Algebra using (CommutativeSemiring)
open import Relation.Binary

module Polynomials.CommutativeSemiring.Expr
  {a ℓ}
  (commutativeSemiring : CommutativeSemiring a ℓ)
  (_≟C_ : Decidable (CommutativeSemiring._≈_ commutativeSemiring))
  where

open CommutativeSemiring commutativeSemiring hiding (zero)
open import Data.Fin as Fin using (Fin)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec)

infixl 6 _⊕_
infixl 7 _⊗_
data Expr : ℕ → Set a where
  Κ : ∀ {n} → Carrier → Expr n
  Ι : ∀ {n} → Fin n → Expr n
  _⊕_ : ∀ {n} → Expr n → Expr n → Expr n
  _⊗_ : ∀ {n} → Expr n → Expr n → Expr n

⟦_⟧ : ∀ {n} → Expr n → Vec Carrier n → Carrier
⟦ Κ x ⟧ ρ = x
⟦ Ι x ⟧ ρ = Vec.lookup x ρ
⟦ x ⊕ y ⟧ ρ = ⟦ x ⟧ ρ + ⟦ y ⟧ ρ
⟦ x ⊗ y ⟧ ρ = ⟦ x ⟧ ρ * ⟦ y ⟧ ρ

open import Polynomials.CommutativeSemiring.Normal commutativeSemiring _≟C_
  using (Poly; _⊞_; _⊠_; κ; ι)
  renaming (⟦_⟧ to ⟦_⟧ₚ)

norm : ∀ {n} → Expr n → Poly n
norm (Κ x) = κ x
norm (Ι x) = ι x
norm (x ⊕ y) = norm x ⊞ norm y
norm (x ⊗ y) = norm x ⊠ norm y

⟦_⇓⟧ : ∀ {n} → Expr n → Vec Carrier n → Carrier
⟦ x ⇓⟧ = ⟦ norm x ⟧ₚ

import Polynomials.CommutativeSemiring.Homomorphism commutativeSemiring _≟C_ as Hom
open import Function

correct : ∀ {n} (e : Expr n) ρ → ⟦ e ⇓⟧ ρ ≈ ⟦ e ⟧ ρ
correct (Κ x) ρ = Hom.κ-hom x ρ
correct (Ι x) ρ = Hom.ι-hom x ρ
correct (x ⊕ y) ρ = Hom.⊞-hom (norm x) (norm y) ρ ⟨ trans ⟩ (correct x ρ ⟨ +-cong ⟩ correct y ρ)
correct (x ⊗ y) ρ = Hom.⊠-hom (norm x) (norm y) ρ ⟨ trans ⟩ (correct x ρ ⟨ *-cong ⟩ correct y ρ)

open import Relation.Binary.Reflection setoid Ι ⟦_⟧ ⟦_⇓⟧ correct public
