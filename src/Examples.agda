module Examples where

module New where
  open import Polynomial.Simple.AlmostCommutativeRing
  open import Polynomial.Simple.Reflection
  open import Data.Nat as ℕ using (ℕ; suc; zero)
  open import Data.Nat.Properties
  open import Level using (0ℓ)

  NatRing : AlmostCommutativeRing 0ℓ 0ℓ
  NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_

  open AlmostCommutativeRing NatRing

  lemma : ∀ x y → (x ^ 100) * (y ^ 100) ≈ (y ^ 100) * (x ^ 100)
  lemma = solve NatRing

module Old where
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat
  open import Data.Nat.Solver using (module +-*-Solver)
  open +-*-Solver

  lemma : ∀ x y → (x ^ 100) * (y ^ 100) ≡ (y ^ 100) * (x ^ 100)
  lemma = solve 2 (λ x y → ((x :^ 100) :* (y :^ 100)) := ((y :^ 100) :* (x :^ 100))) refl
