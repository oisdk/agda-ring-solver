module Examples where

open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.Reflection
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Level using (0ℓ)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (refl)

NatRing : AlmostCommutativeRing 0ℓ 0ℓ
NatRing = fromCommutativeSemiring *-+-commutativeSemiring λ { zero → just refl ; (suc x) → nothing}
-- open import Relation.Traced

-- rng : _
-- rng = tracedRing NatRing

open AlmostCommutativeRing NatRing


lemma : ∀ v w x y z → (v + w + x + y + z) ^ 5 ≈ (v + w + x + y + z) ^ 5
lemma = solve NatRing

-- open import Data.List
-- open import Data.String

-- example : List _
-- example = showProof NatRing (lemma 10 20)

-- ~ 30 seconds
-- module Old where
--   open import Relation.Binary.PropositionalEquality
--   open import Data.Nat
--   open import Data.Nat.Solver using (module +-*-Solver)
--   open +-*-Solver

--   lemma : ∀ x y → (x ^ 400) * (y ^ 400) ≡ (y ^ 400) * (x ^ 400)
--   lemma = solve 2 (λ x y → ((x :^ 400) :* (y :^ 400)) := ((y :^ 400) :* (x :^ 400))) refl
