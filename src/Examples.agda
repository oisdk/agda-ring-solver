module Examples where

open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.Reflection
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Level using (0ℓ)

NatRing : AlmostCommutativeRing 0ℓ 0ℓ
NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_
open import Relation.Traced NatRing

open AlmostCommutativeRing tracedRing

lemma : ∀ x y → x + y ≈ y + x
lemma = solve tracedRing

open import Data.List
open import Data.String

example : List _
example = showProof (lemma 1 2)

-- ~ 30 seconds
-- module Old where
--   open import Relation.Binary.PropositionalEquality
--   open import Data.Nat
--   open import Data.Nat.Solver using (module +-*-Solver)
--   open +-*-Solver

--   lemma : ∀ x y → (x ^ 400) * (y ^ 400) ≡ (y ^ 400) * (x ^ 400)
--   lemma = solve 2 (λ x y → ((x :^ 400) :* (y :^ 400)) := ((y :^ 400) :* (x :^ 400))) refl
