module Benchmarks where
open import Data.Nat using (ℕ)


open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver
lemma : ∀ v w x y z → (v + w + x + y + z) ^ 4 ≡ (v + w + x + y + z) ^ 4
lemma = solve 5 (λ v w x y z → (v :+ w :+ x :+ y :+ z) :^ 4 := (v :+ w :+ x :+ y :+ z) :^ 4) refl