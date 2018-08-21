open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Ring.Homomorphism.K
  {r₁ r₂ r₃ r₄}
  (coeff : RawRing r₁)
  (Zero-C : Pred (RawRing.Carrier coeff) r₂)
  (zero-c? : Decidable Zero-C)
  (ring : AlmostCommutativeRing r₃ r₄)
  (morphism : coeff -Raw-AlmostCommutative⟶ ring)
  (Zero-C⟶Zero-R : ∀ x → Zero-C x → AlmostCommutativeRing._≈_ ring (_-Raw-AlmostCommutative⟶_.⟦_⟧ morphism x) (AlmostCommutativeRing.0# ring))
  where

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
open import Data.Empty

1+n≰n : ∀ {n} → 1 ℕ.+ n ℕ.≰ n
1+n≰n (ℕ.s≤s le) = 1+n≰n le

≤-step : ∀ {m n} → m ℕ.≤ n → m ℕ.≤ 1 ℕ.+ n
≤-step ℕ.z≤n       = ℕ.z≤n
≤-step (ℕ.s≤s m≤n) = ℕ.s≤s (≤-step m≤n)

≤-refl : ∀ {m} → m ℕ.≤ m
≤-refl {zero}  = ℕ.z≤n
≤-refl {suc m} = ℕ.s≤s (≤-refl {m})

≤′⇒≤ : ∀ {x y} → x ≤ y → x ℕ.≤ y
≤′⇒≤ m≤m       = ≤-refl
≤′⇒≤ (≤-s m≤n) = ≤-step (≤′⇒≤ m≤n)

≤-irrel : ∀ {i n}
        → (x : i ≤ n)
        → (y : i ≤ n)
        → (x ≡.≡ y)
≤-irrel m≤m m≤m = ≡.refl
≤-irrel (≤-s x) (≤-s y) = ≡.cong ≤-s (≤-irrel x y)
≤-irrel (≤-s x) m≤m = ⊥-elim (1+n≰n (≤′⇒≤ x))
≤-irrel m≤m (≤-s x) = ⊥-elim (1+n≰n (≤′⇒≤ x))
