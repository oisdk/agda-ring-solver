module Polynomial.Simple.Solver where

open import Polynomial.Expr public
open import Polynomial.Simple.AlmostCommutativeRing public
open import Data.Vec
open import Algebra.Solver.Ring.AlmostCommutativeRing using (-raw-almostCommutative⟶)
open import Polynomial.Parameters
open import Function

open import Data.Vec.N-ary

module Ops {ℓ₁ ℓ₂} (ring : AlmostCommutativeRing ℓ₁ ℓ₂) where
  open AlmostCommutativeRing ring
  ⟦_⟧ : ∀ {n} → Expr Carrier n → Vec Carrier n → Carrier
  ⟦ Κ x ⟧ ρ = x
  ⟦ Ι x ⟧ ρ = lookup x ρ
  ⟦ x ⊕ y ⟧ ρ = ⟦ x ⟧ ρ + ⟦ y ⟧ ρ
  ⟦ x ⊗ y ⟧ ρ = ⟦ x ⟧ ρ * ⟦ y ⟧ ρ
  ⟦ ⊝ x ⟧ ρ = - ⟦ x ⟧ ρ

  rawCoeff : RawCoeff ℓ₁ ℓ₂
  rawCoeff = record
    { coeffs = rawRing
    ; Zero-C = 0# ≈_
    ; zero-c? = 0# ≟_
    }
  open import Polynomial.Normal.Definition rawCoeff
  open import Polynomial.Normal.Operations rawCoeff

  norm : ∀ {n} → Expr Carrier n → Poly n
  norm = go
    where
    go : ∀ {n} → Expr Carrier n → Poly n
    go (Κ x) = κ x
    go (Ι x) = ι x
    go (x ⊕ y) = go x ⊞ go y
    go (x ⊗ y) = go x ⊠ go y
    go (⊝ x) = ⊟ go x

  import Algebra.Solver.Ring.AlmostCommutativeRing as UnDec

  complex : UnDec.AlmostCommutativeRing ℓ₁ ℓ₂
  complex = record
    { isAlmostCommutativeRing = record
        { isCommutativeSemiring = isCommutativeSemiring
        ; -‿cong = -‿cong
        ; -‿*-distribˡ = -‿*-distribˡ
        ; -‿+-comm = -‿+-comm
        }
    }

  homo : Homomorphism ℓ₁ ℓ₂ ℓ₁ ℓ₂
  homo = record
    { coeffs = rawCoeff
    ; ring = complex
    ; morphism = UnDec.-raw-almostCommutative⟶ complex
    ; Zero-C⟶Zero-R = λ x z → sym z
    }

  ⟦_⇓⟧ : ∀ {n} → Expr Carrier n → Vec Carrier n → Carrier
  ⟦ expr ⇓⟧ = ⟦ norm expr ⟧ₚ where

    open import Polynomial.Normal.Semantics homo
      renaming (⟦_⟧ to ⟦_⟧ₚ)

  correct : ∀ {n} (expr : Expr Carrier n) ρ → ⟦ expr ⇓⟧ ρ ≈ ⟦ expr ⟧ ρ
  correct {n = n} = go
    where
    open import Polynomial.Homomorphism homo

    go : ∀ (expr : Expr Carrier n) ρ → ⟦ expr ⇓⟧ ρ ≈ ⟦ expr ⟧ ρ
    go (Κ x) ρ = κ-hom x ρ
    go (Ι x) ρ = ι-hom x ρ
    go (x ⊕ y) ρ = ⊞-hom (norm x) (norm y) ρ ⟨ trans ⟩ (go x ρ ⟨ +-cong ⟩ go y ρ)
    go (x ⊗ y) ρ = ⊠-hom (norm x) (norm y) ρ ⟨ trans ⟩ (go x ρ ⟨ *-cong ⟩ go y ρ)
    go (⊝ x) ρ = ⊟-hom (norm x) ρ ⟨ trans ⟩ -‿cong (go x ρ)

  open import Relation.Binary.Reflection setoid Ι ⟦_⟧ ⟦_⇓⟧ correct public

open import Data.Nat using (ℕ)
open import Data.Product

solve : ∀ {ℓ₁ ℓ₂}
      → (ring : AlmostCommutativeRing ℓ₁ ℓ₂)
      → (n : ℕ)
      → (f : N-ary n (Expr (AlmostCommutativeRing.Carrier ring) n) (Expr (AlmostCommutativeRing.Carrier ring) n × Expr (AlmostCommutativeRing.Carrier ring) n))
      → Eqʰ n (AlmostCommutativeRing._≈_ ring) (curryⁿ (Ops.⟦_⇓⟧ ring  (proj₁ (Ops.close ring n f)))) (curryⁿ (Ops.⟦_⇓⟧ ring (proj₂ (Ops.close ring n f))))
      → Eq  n (AlmostCommutativeRing._≈_ ring) (curryⁿ (Ops.⟦_⟧ ring (proj₁ (Ops.close ring n f)))) (curryⁿ (Ops.⟦_⟧ ring (proj₂ (Ops.close ring n f))))
solve ring = solve′
  where
  open Ops ring renaming (solve to solve′)

_⊜_ : ∀ {ℓ₁ ℓ₂}
    → (ring : AlmostCommutativeRing ℓ₁ ℓ₂)
    → (n : ℕ)
    → Expr (AlmostCommutativeRing.Carrier ring) n
    → Expr (AlmostCommutativeRing.Carrier ring) n
    → Expr (AlmostCommutativeRing.Carrier ring) n × Expr (AlmostCommutativeRing.Carrier ring) n
_⊜_ _ _ = _,_
