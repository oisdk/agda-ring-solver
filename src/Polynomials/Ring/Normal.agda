open import Algebra
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Relation.Unary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.List as List using (List; []; _∷_)
open import Level using (lift)
open import Data.Product

open import Polynomials.Ring.Normal.Parameters

module Polynomials.Ring.Normal
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open Homomorphism homo

open import Data.Nat.Order.Gappy public
open import Polynomials.Ring.Normal.Definition coeffs public
open import Polynomials.Ring.Normal.Construction coeffs public
open import Polynomials.Ring.Normal.Operations coeffs public
open import Polynomials.Ring.Normal.Semantics homo public
