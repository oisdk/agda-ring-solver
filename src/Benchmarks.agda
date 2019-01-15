module Benchmarks where

module Old where
  open import Data.Nat as ℕ using (ℕ; suc; zero)
  open import Data.Nat.Properties using (*-+-commutativeSemiring)
  open import Algebra.Solver.Ring.AlmostCommutativeRing
  open import Algebra.Solver.Ring.Simple (fromCommutativeSemiring *-+-commutativeSemiring) ℕ._≟_
  import Data.Fin as Fin
  import Data.Vec as Vec

  example : ℕ → ℕ → ℕ
  example x y = ⟦ (var Fin.zero :+ var (Fin.suc Fin.zero)) :^ 2 ⟧ (x Vec.∷ y Vec.∷ Vec.[])

module New where
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

  example : ℕ → ℕ → ℕ
  example x y = ⟦ (ι Fin.zero ⊞ ι (Fin.suc Fin.zero)) ⊡ 2 ⟧ (x Vec.∷ y Vec.∷ Vec.[])

open import Data.Nat.Show
open import IO.Primitive using (IO; putStrLn)
open import Data.String using (String)
open import Codata.Musical.Costring using (toCostring)
open import Foreign.Haskell using (Unit)

open Old using (example)

main : IO Unit
main = putStrLn (toCostring (show (example 3 4)))
