module Examples where
open import Data.Nat using (ℕ)

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

  lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
  lemma₁ = solve NatRing


-- module Old where
--   open import Relation.Binary.PropositionalEquality
--   open import Data.Nat
--   open import Data.Nat.Solver using (module +-*-Solver)
--   open +-*-Solver

--   lemma : _
--   lemma = solve 5 (λ v w x y z → (con 1 :+ v :^ 1 :+ w :^ 2 :+ x :^ 3 :+ y :^ 4 :+ z :^ 5) :^ d := (con 1 :+ v :^ 1 :+ w :^ 2 :+ x :^ 3 :+ y :^ 4 :+ z :^ 5) :^ d) refl
