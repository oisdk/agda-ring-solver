{-# OPTIONS --without-K #-}

open import Algebra.Solver.Ring.AlmostCommutativeRing

module Polynomials.ByConstruction
  {a ℓ}
  (coeffs : AlmostCommutativeRing a ℓ)
  where

open import Level
open import Function

module Context where
  open AlmostCommutativeRing coeffs
  open import Relation.Binary

  Fn : Set a
  Fn = Carrier → Carrier

  infix 4 _≋_
  _≋_ : Fn → Fn → Set (a ⊔ ℓ)
  x ≋ y = ∀ ρ → x ρ ≈ y ρ

  ≋-equiv : IsEquivalence _≋_
  ≋-equiv = record
    { refl = λ ρ → refl
    ; sym  = λ x≈y ρ → sym (x≈y ρ)
    ; trans = λ x≈y y≈z ρ → trans (x≈y ρ) (y≈z ρ)
    }

  exprRing : AlmostCommutativeRing a (a ⊔ ℓ)
  exprRing = record
    { Carrier = Fn
    ; _≈_     = _≋_
    ; _+_     = λ x y ρ → x ρ + y ρ
    ; _*_     = λ x y ρ → x ρ * y ρ
    ; -_      = λ x ρ → - x ρ
    ; 0#      = λ _ → 0#
    ; 1#      = λ _ → 1#
    ; isAlmostCommutativeRing = record
      { -‿cong                = λ xρ≈yρ ρ → -‿cong (xρ≈yρ ρ)
      ; -‿*-distribˡ          = λ x y ρ → -‿*-distribˡ (x ρ) (y ρ)
      ; -‿+-comm              = λ x y ρ → -‿+-comm (x ρ) (y ρ)
      ; isCommutativeSemiring = record
        { zeroˡ = λ x ρ → zeroˡ (x ρ)
        ; distribʳ = λ x y z ρ → distribʳ (x ρ) (y ρ) (z ρ)
        ; +-isCommutativeMonoid = record
          { identityˡ = λ x ρ → +-identityˡ (x ρ)
          ; comm = λ x y ρ → +-comm (x ρ) (y ρ)
          ; isSemigroup = record
            { assoc = λ x y z ρ → +-assoc (x ρ) (y ρ) (z ρ)
            ; ∙-cong = λ x₁≈x₂ y₁≈y₂ ρ → +-cong (x₁≈x₂ ρ) (y₁≈y₂ ρ)
            ; isEquivalence = ≋-equiv
            }
          }
        ; *-isCommutativeMonoid = record
          { identityˡ = λ x ρ → *-identityˡ (x ρ)
          ; comm = λ x y ρ → *-comm (x ρ) (y ρ)
          ; isSemigroup = record
            { assoc = λ x y z ρ → *-assoc (x ρ) (y ρ) (z ρ)
            ; ∙-cong = λ x₁≈x₂ y₁≈y₂ ρ → *-cong (x₁≈x₂ ρ) (y₁≈y₂ ρ)
            ; isEquivalence = ≋-equiv
            }
          }
        }
      }
    }

module Lemmas where
  open AlmostCommutativeRing coeffs
  open import Polynomials.Ring.Reasoning coeffs

  +-distrib : ∀ {x xs y ys} ρ → (x + ρ * xs) + (y + ρ * ys) ≈ x + y + ρ * (xs + ys)
  +-distrib {x} {xs} {y} {ys} ρ =
    begin
      (x + ρ * xs) + (y + ρ * ys)
    ≈⟨ +-assoc x _ _ ⟩
      x + (ρ * xs + (y + ρ * ys))
    ≈⟨ refl ⟨ +-cong ⟩ (sym (+-assoc _ y _) ⟨ trans ⟩ ( +-comm _ y ⟨ +-cong ⟩ refl ⟨ trans ⟩ +-assoc _ _ _)) ⟩
      x + (y + (ρ * xs + ρ * ys))
    ≈⟨ sym (+-assoc x y _) ⟩
      x + y + (ρ * xs + ρ * ys)
    ≈⟨ refl ⟨ +-cong ⟩ sym (distribˡ ρ xs ys) ⟩
      x + y + ρ * (xs + ys)
    ∎

  ⋊-distrib : ∀ x y ys ρ → x * (y + ρ * ys) ≈ x * y + ρ * (x * ys)
  ⋊-distrib x y ys ρ =
    begin
      x * (y + ρ * ys)
    ≈⟨ distribˡ x y _ ⟩
      x * y + x * (ρ * ys)
    ≈⟨ +≫ (sym (*-assoc x ρ ys) ︔ (≪* *-comm x ρ) ︔ *-assoc _ _ _) ⟩
      x * y + ρ * (x * ys)
    ∎

open Lemmas
open Context
open AlmostCommutativeRing exprRing
module Coeff = AlmostCommutativeRing coeffs
open import Polynomials.Ring.Reasoning exprRing
-- This looks a lot like ALGEBRAIC ORNAMENTATION

data Poly : Carrier → Set (a ⊔ ℓ) where
  ⟦⟧ : Poly 0#
  ⟦_∷_⟧ : ∀ x {xs} → Poly xs → Poly (λ ρ → x Coeff.+ ρ Coeff.* xs ρ)

infixr 0 _⇐_
record Expr (expr : Carrier) : Set (a ⊔ ℓ) where
  constructor _⇐_
  field
    {norm} : Carrier
    poly   : Poly norm
    proof  : expr ≋ norm

infixr 0 _⟸_
_⟸_ : ∀ {x y} → x ≋ y → Expr y → Expr x
_⟸_ x≋y (xs ⇐ xp) = xs ⇐ x≋y ⟨ trans ⟩ xp

_⊞_ : ∀ {x y} → Expr x → Expr y → Expr (x + y)
(x ⇐ xp) ⊞ (y ⇐ yp) = xp ⟨ +-cong ⟩ yp ⟸ x ⊕ y
  where
  _⊕_ : ∀ {x y} → Poly x → Poly y → Expr (x + y)
  ⟦⟧ ⊕ ys = ys ⇐ +-identityˡ _
  ⟦ x ∷ xs ⟧ ⊕ ⟦⟧ = ⟦ x ∷ xs ⟧ ⇐ +-identityʳ _
  ⟦ x ∷ xs ⟧ ⊕ ⟦ y ∷ ys ⟧ with xs ⊕ ys
  ... | zs ⇐ zp = ⟦ x Coeff.+ y ∷ zs ⟧ ⇐
      (λ ρ → +-distrib ρ)
    ⟨ trans ⟩
      (refl ⟨ +-cong ⟩ (refl ⟨ *-cong ⟩ zp))
