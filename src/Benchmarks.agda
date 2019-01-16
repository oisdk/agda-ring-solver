module Benchmarks where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Fin as Fin using (Fin)
open import Data.Fin.Literals as FinLit
open import Data.Nat.Literals as NatLit
open import Agda.Builtin.FromNat using (Number)

instance
  finLit : ∀ {n} → Number (Fin n)
  finLit = FinLit.number _

instance
  natLit : Number ℕ
  natLit = NatLit.number

d : ℕ
d = 5

module Old where
  open import Data.Nat.Properties using (*-+-commutativeSemiring)
  open import Algebra.Solver.Ring.AlmostCommutativeRing
  open import Algebra.Solver.Ring.Simple (fromCommutativeSemiring *-+-commutativeSemiring) ℕ._≟_
  open import Data.Vec as Vec using (_∷_; [])

  dub : ∀ {n} → Polynomial n → Polynomial n
  dub x = x :+ x

  example : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  example v w x y z = ⟦ ((con 1 :+ (var 0 :^ d)) :+ (var 1 :^ d) :+ (var 2 :^ d) :+ (var 3 :^ d) :+ (var 4 :^ d)) :^ d  ⟧↓ (v ∷ w ∷ x ∷ y ∷ z ∷ [])

module New where
  open import Polynomial.Simple.AlmostCommutativeRing
  open import Polynomial.Parameters
  open import Data.Nat.Properties using (*-+-commutativeSemiring)
  open import Data.Vec as Vec using (_∷_; [])

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

  dub : ∀ {n} → Poly n → Poly n
  dub x = x ⊞ x

  example : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  example v w x y z = ⟦ ((κ 1 ⊞ (ι 0 ⊡ d)) ⊞ (ι 1 ⊡ d) ⊞ (ι 2 ⊡ d) ⊞ (ι 3 ⊡ d) ⊞ (ι 4 ⊡ d)) ⊡ d ⟧ (v ∷ w ∷ x ∷ y ∷ z ∷ [])

open import IO.Primitive using (IO; putStrLn)
open import Foreign.Haskell using (Unit)

postulate
  printNat : ℕ → IO Unit

{-# COMPILE GHC printNat = print #-}

open Old using (example)

main : IO Unit
main = printNat (example 3 4 5 6 7)
