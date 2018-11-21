open import Polynomials.Normal.Parameters

module Polynomials.Normal
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open Homomorphism homo
open import Data.Nat.Order.Gappy public
open import Polynomials.Normal.Definition coeffs public
open import Polynomials.Normal.Construction coeffs public
open import Polynomials.Normal.Operations coeffs public
open import Polynomials.Normal.Semantics homo public
