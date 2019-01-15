module Benchmarks where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Parameters
open import Data.Nat.Properties using (*-+-commutativeSemiring)

NatRing : AlmostCommutativeRing _ _
NatRing = fromCommutativeSemiring *-+-commutativeSemiring ℕ._≟_

open import Relation.Binary.PropositionalEquality

natCoeff : RawCoeff _ _
natCoeff = record
  { coeffs = AlmostCommutativeRing.rawRing NatRing
  ; Zero-C = _≡_ 0
  ; zero-c? = ℕ._≟_ 0
  }

open AlmostCommutativeRing NatRing
import Algebra.Solver.Ring.AlmostCommutativeRing as UnDec

complex : UnDec.AlmostCommutativeRing _ _
complex = record
  { isAlmostCommutativeRing = record
    { isCommutativeSemiring = isCommutativeSemiring
    ; -‿cong = -‿cong
    ; -‿*-distribˡ = -‿*-distribˡ
    ; -‿+-comm = -‿+-comm
    }
  }

open import Function

homo : Homomorphism _ _ _ _
homo = record
  { coeffs = natCoeff
  ; ring = complex
  ; morphism = UnDec.-raw-almostCommutative⟶ complex
  ; Zero-C⟶Zero-R = id
  }

open import Polynomial.NormalForm homo
import Data.Fin as Fin
import Data.Vec as Vec

example₁ : ℕ → ℕ → ℕ
example₁ x y = ⟦ ι Fin.zero ⊞ ι (Fin.suc Fin.zero) ⟧ (x Vec.∷ y Vec.∷ Vec.[])

open import Data.Nat.Show

open import IO.Primitive using (IO; putStrLn)
open import Data.String using (String)
open import Codata.Musical.Costring using (toCostring)
open import Foreign.Haskell using (Unit)

main : IO Unit
main = putStrLn (toCostring (show (example₁ 3 4)))



-- open import Polynomial.Simple.Reflection
-- open import Data.Nat as ℕ using (ℕ; suc; zero)
-- open import Level using (0ℓ)

-- open import Relation.Traced

-- rng : _
-- rng = tracedRing NatRing

-- open AlmostCommutativeRing rng


-- lemma : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
-- lemma = solve rng

-- open import Data.List
-- open import Data.String

-- example : List _
-- example = showProof NatRing (lemma 10 20)

-- -- ~ 30 seconds
-- -- module Old where
-- --   open import Relation.Binary.PropositionalEquality
-- --   open import Data.Nat
-- --   open import Data.Nat.Solver using (module +-*-Solver)
-- --   open +-*-Solver

-- --   lemma : ∀ x y → (x ^ 400) * (y ^ 400) ≡ (y ^ 400) * (x ^ 400)
-- --   lemma = solve 2 (λ x y → ((x :^ 400) :* (y :^ 400)) := ((y :^ 400) :* (x :^ 400))) refl
