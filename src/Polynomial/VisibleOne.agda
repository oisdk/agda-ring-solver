{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters

module Polynomial.VisibleOne
  {ℓ₁ ℓ₂ ℓ₃}
  (homo : Homomorphism ℓ₁ ℓ₂ ℓ₃)
  where

open import Data.Bool using (Bool; true; false)
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Function

open RawCoeff (Homomorphism.coeffs homo)

-- This module provides a wrapper type for the coefficients of
-- a polynomial, which has the single purpose of avoiding
-- multiplying by 1.

data 1*x*1 : Set ℓ₁ where
  1* : 1*x*1
  ⟨_⟩ : Carrier → 1*x*1

⟦_⟧-1 : 1*x*1 → Carrier
⟦ 1* ⟧-1 = 1#
⟦ ⟨ x ⟩ ⟧-1 = x

1-coeff : RawCoeff ℓ₁
1-coeff = record
  { coeffs = record
    { Carrier = 1*x*1
    ; _+_ = λ x y → ⟨ ⟦ x ⟧-1 + ⟦ y ⟧-1 ⟩
    ; _*_ = λ { 1* y → y ; ⟨ x ⟩ 1* → ⟨ x ⟩ ; ⟨ x ⟩ ⟨ y ⟩ → ⟨ x * y ⟩}
    ; -_  = λ x → ⟨ - ⟦ x ⟧-1 ⟩
    ; 0#  = ⟨ 0# ⟩
    ; 1#  = 1*
    }
  ; Zero-C = λ { 1* → false ; ⟨ x ⟩ → Zero-C x}
  }

open _-Raw-AlmostCommutative⟶_
open IsAlmostCommutativeRing (Homomorphism.isAlmostCommutativeRing homo)

1-morph : (RawCoeff.coeffs 1-coeff) -Raw-AlmostCommutative⟶ (Homomorphism.ring homo)
⟦ 1-morph ⟧ x = Homomorphism.⟦ homo ⟧ᵣ ⟦ x ⟧-1
+-homo 1-morph x y = Homomorphism.+-homo homo ⟦ x ⟧-1 ⟦ y ⟧-1
*-homo 1-morph 1* y = sym (trans (*-cong (Homomorphism.1-homo homo) refl) (*-identityˡ _))
*-homo 1-morph ⟨ x ⟩ 1* = sym (trans (*-cong refl (Homomorphism.1-homo homo)) (*-identityʳ _))
*-homo 1-morph ⟨ x ⟩ ⟨ y ⟩ = Homomorphism.*-homo homo x y
-‿homo 1-morph x = Homomorphism.-‿homo homo ⟦ x ⟧-1
0-homo 1-morph = Homomorphism.0-homo homo
1-homo 1-morph = Homomorphism.1-homo homo

1*-homo : Homomorphism ℓ₁ ℓ₂ ℓ₃
1*-homo = record
  { coeffs = 1-coeff
  ; ring = Homomorphism.ring homo
  ; morphism = 1-morph
  ; Zero-C⟶Zero-R = λ { 1* → λ () ; ⟨ x ⟩ → Homomorphism.Zero-C⟶Zero-R homo x}
  }
