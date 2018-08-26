module Algebra.Ring.Traced where

open import Data.String
open import Data.Nat as ℕ using (ℕ)
open import Algebra.Solver.Ring.AlmostCommutativeRing
import Level

infixl 6 _⊕_
infixl 7 _⊗_
data Expr : Set where
  ι : String → Expr
  κ : ℕ → Expr
  _⊕_ : Expr → Expr → Expr
  _⊗_ : Expr → Expr → Expr
  ⊝_ : Expr → Expr

open import Relation.Binary.Traced Expr public

ring : AlmostCommutativeRing Level.zero Level.zero
ring = record
  { Carrier = Expr
  ; _≈_ = _≡⋯≡_
  ; _+_ = _⊕_
  ; _*_ = _⊗_
  ; -_  = ⊝_
  ; 0#  = κ 0
  ; 1#  = κ 1
  ; isAlmostCommutativeRing = record
      { -‿cong                = λ x≡y → cong₁ "-‿cong" x≡y [refl]
      ; -‿*-distribˡ          = λ _ _ → _ ≡⟨ "-‿*-distribˡ" ⟩ [refl]
      ; -‿+-comm              = λ _ _ → _ ≡⟨ "-‿+-comm" ⟩ [refl]
      ; isCommutativeSemiring = record
        { zeroˡ = λ x → _ ≡⟨ "zeroˡ" ⟩ [refl]
        ; distribʳ = λ _ _ _ → _ ≡⟨ "distribʳ" ⟩ [refl]
        ; +-isCommutativeMonoid = record
          { identityˡ = λ _ → _ ≡⟨ "+-identityˡ" ⟩ [refl]
          ; comm = λ _ _ → _ ≡⟨ "+-comm" ⟩ [refl]
          ; isSemigroup = record
            { assoc = λ _ _ _ → _ ≡⟨ "+-assoc" ⟩ [refl]
            ; ∙-cong = λ xp yp → cong₂ "+-cong" xp yp [refl]
            ; isEquivalence = ≡⋯≡-equiv
            }
          }
        ; *-isCommutativeMonoid = record
          { identityˡ = λ _ → _ ≡⟨ "*-identityˡ" ⟩ [refl]
          ; comm = λ _ _ → _ ≡⟨ "*-comm" ⟩ [refl]
          ; isSemigroup = record
            { assoc = λ _ _ _ → _ ≡⟨ "*-assoc" ⟩ [refl]
            ; ∙-cong = λ xp yp → cong₂ "*-cong" xp yp [refl]
            ; isEquivalence = ≡⋯≡-equiv
            }
          }
        }
      }
  }
