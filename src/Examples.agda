module Examples where

open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.Reflection
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Level using (0ℓ)

NatRing : AlmostCommutativeRing 0ℓ 0ℓ
NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_

open AlmostCommutativeRing NatRing

lemma : ∀ w x y z → (w * 100000) + (y + x + z) * 1000 ≈ 1000 * (z + x + y) + (100000 * w)
lemma = solve NatRing
