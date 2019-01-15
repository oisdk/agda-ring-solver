module Benchmarks where

open import Data.Nat as ℕ using (ℕ; suc; zero)

d : ℕ
d = 6

-- module Old where
--   open import Data.Nat.Properties using (*-+-commutativeSemiring)
--   open import Algebra.Solver.Ring.AlmostCommutativeRing
--   open import Algebra.Solver.Ring.Simple (fromCommutativeSemiring *-+-commutativeSemiring) ℕ._≟_
--   import Data.Fin as Fin
--   import Data.Vec as Vec

--   example : ℕ → ℕ → ℕ → ℕ
--   example x y z = ⟦ ((var Fin.zero :^ d) :+ (var (Fin.suc Fin.zero) :^ d) :+ (var (Fin.suc (Fin.suc Fin.zero)) :^ d)) :^ 2 ⟧ (x Vec.∷ y Vec.∷ z Vec.∷ Vec.[])

module New where
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

  example : ℕ → ℕ → ℕ → ℕ
  example x y z = ⟦ ((ι Fin.zero ⊡ d) ⊞ (ι (Fin.suc Fin.zero) ⊡ d) ⊞ (ι (Fin.suc (Fin.suc Fin.zero)) ⊡ d)) ⊡ 2 ⟧ (x Vec.∷ y Vec.∷ z Vec.∷ Vec.[])

open import IO.Primitive using (IO; putStrLn)
open import Data.String using (String)
open import Codata.Musical.Costring using (toCostring)
open import Foreign.Haskell using (Unit)

postulate
  printNat : ℕ → IO Unit

{-# COMPILE GHC printNat = print #-}

open New using (example)

main : IO Unit
main = printNat (example 3 4 5)
