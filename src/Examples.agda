module Examples where

open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.Reflection
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Level using (0ℓ)

NatRing : AlmostCommutativeRing 0ℓ 0ℓ
NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_

open AlmostCommutativeRing NatRing

lemma : ∀ w x y z → (w * 10) + (y + x + z) * 10 ≈ 10 * (z + x + y) + (10 * w)
lemma = solve NatRing
