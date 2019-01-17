module Examples where
open import Data.Nat using (ℕ)

d : ℕ
d = 1

-- module New where
--   open import Polynomial.Simple.AlmostCommutativeRing
--   open import Polynomial.Simple.Reflection
--   open import Data.Nat using (ℕ; suc; zero)
--   open import Data.Nat.Properties
--   open import Level using (0ℓ)
--   open import Data.Maybe
--   open import Relation.Binary.PropositionalEquality using (refl)

--   NatRing : AlmostCommutativeRing 0ℓ 0ℓ
--   NatRing = fromCommutativeSemiring *-+-commutativeSemiring λ { zero → just refl ; (suc x) → nothing}

--   open AlmostCommutativeRing NatRing

--   lemma : ∀ x y z → (x ^ d + y ^ d + z ^ d) ≈ (x ^ d + y ^ d + z ^ d)
--   lemma = solve NatRing

module Old where
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat
  open import Data.Nat.Solver using (module +-*-Solver)
  open +-*-Solver

  lemma : _
  lemma = solve 3 (λ x y z → (x :^ d :+ y :^ d :+ z :^ d) := (x :^ d :+ y :^ d :+ z :^ d)) refl
