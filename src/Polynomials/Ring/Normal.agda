open import Algebra
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Relation.Unary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Data.List as List using (List; []; _∷_)
open import Level using (lift)
open import Data.Product

module Polynomials.Ring.Normal
  {r₁ r₂ r₃ r₄}
  (coeff : RawRing r₁)
  (Zero-C : Pred (RawRing.Carrier coeff) r₂)
  (zero-c? : Decidable Zero-C)
  (ring : AlmostCommutativeRing r₃ r₄)
  (morphism : coeff -Raw-AlmostCommutative⟶ ring)
  where

open import Data.Nat.Order.Gappy public
open import Polynomials.Ring.Normal.Definition coeff Zero-C zero-c? public
open import Polynomials.Ring.Normal.Operations coeff Zero-C zero-c? public
open import Polynomials.Ring.Normal.Semantics coeff Zero-C zero-c? ring morphism public
