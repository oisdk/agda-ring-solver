{-# OPTIONS --without-K --safe #-}

module Polynomial.Simple.AlmostCommutativeRing.Instances where

open import Polynomial.Simple.AlmostCommutativeRing
open import Level using (0ℓ)

module Nat where
  open import Data.Nat using (zero; suc)
  open import Relation.Binary.PropositionalEquality using (refl)
  open import Data.Nat.Properties using (*-+-commutativeSemiring)
  open import Data.Maybe using (just; nothing)

  ring : AlmostCommutativeRing 0ℓ 0ℓ
  ring =
    fromCommutativeSemiring
      *-+-commutativeSemiring
      λ { zero → just refl; _ → nothing }

module Int where
  open import Data.Nat using (zero)
  open import Data.Integer using (+_)
  open import Data.Integer.Properties using(+-*-commutativeRing)
  open import Data.Maybe using (just; nothing)
  open import Relation.Binary.PropositionalEquality using (refl)

  ring : AlmostCommutativeRing 0ℓ 0ℓ
  ring =
    fromCommutativeRing
      +-*-commutativeRing
      λ { (+ zero) → just refl; _ → nothing }
