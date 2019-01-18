module Examples where
open import Data.Nat using (ℕ)

d : ℕ
d = 8

module New where
  open import Polynomial.Simple.AlmostCommutativeRing
  open import Polynomial.Simple.Reflection
  open import Data.Nat using (ℕ; suc; zero)
  open import Data.Nat.Properties
  open import Level using (0ℓ)
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality using (refl)

  NatRing : AlmostCommutativeRing 0ℓ 0ℓ
  NatRing = fromCommutativeSemiring *-+-commutativeSemiring λ { zero → just refl ; (suc x) → nothing}

  open AlmostCommutativeRing NatRing

  lemma₁ : ∀ v w x y z → (v + w + x + y + z) ^ d ≈ (v + w + x + y + z) ^ d
  lemma₁ = solve NatRing

  -- lemma₂ : ∀ x y z → 1 + x + y ^ 2 + z ^ 3 ≈ 1 + x + y ^ 2 + z ^ 3
  -- lemma₂ = solve NatRing


-- module Old where
--   open import Relation.Binary.PropositionalEquality
--   open import Data.Nat
--   open import Data.Nat.Solver using (module +-*-Solver)
--   open +-*-Solver

--   lemma : _
--   lemma = solve 2 (λ x y → (con 1 :+ x :^ 5 :+ y) :^ d := (con 1 :+ x :^ 5 :+ y) :^ d) refl
