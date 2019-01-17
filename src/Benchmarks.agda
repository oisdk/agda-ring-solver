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
d = 40

module Old where
  open import Data.Nat.Properties using (*-+-commutativeSemiring)
  open import Algebra.Solver.Ring.AlmostCommutativeRing
  open import Algebra.Solver.Ring.Simple (fromCommutativeSemiring *-+-commutativeSemiring) ℕ._≟_
  open import Data.Vec as Vec using (_∷_; [])

  dub : ∀ {n} → Polynomial n → Polynomial n
  dub x = x :+ x

  example : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  example v w x y z = ⟦ (con 1 :+ var 0 :+ var 1 :+ var 2 :+ var 3 :+ var 4) :^ d  ⟧↓ (v ∷ w ∷ x ∷ y ∷ z ∷ [])

module New where
  open import Polynomial.Simple.AlmostCommutativeRing
  open import Polynomial.Parameters
  open import Data.Nat.Properties using (*-+-commutativeSemiring)
  open import Data.Vec as Vec using (_∷_; [])
  open import Data.Maybe
  open import Relation.Binary.PropositionalEquality

  NatRing : AlmostCommutativeRing _ _
  NatRing = fromCommutativeSemiring *-+-commutativeSemiring λ { zero → just refl ; (suc x) → nothing}

  import Polynomial.Simple.Solver
  open import Polynomial.Expr

  open Polynomial.Simple.Solver.Ops NatRing using (⟦_⇓⟧)

  import Data.Fin as Fin
  import Data.Vec as Vec

  example : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
  example v w x y z = ⟦ (Ι 0 ⊕ Ι 1 ⊕ Ι 2 ⊕ Ι 3 ⊕ Ι 4) ⊛ d ⇓⟧ (v ∷ w ∷ x ∷ y ∷ z ∷ [])




open import IO.Primitive using (IO; putStrLn)
open import Foreign.Haskell using (Unit)

postulate
  printNat : ℕ → IO Unit

{-# COMPILE GHC printNat = print #-}

open New using (example)

main : IO Unit
main = printNat (example 3 4 5 6 7)
