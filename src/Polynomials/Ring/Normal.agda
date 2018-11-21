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
