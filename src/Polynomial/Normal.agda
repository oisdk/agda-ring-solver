open import Polynomial.Normal.Parameters

module Polynomial.Normal
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open Homomorphism homo
open import Data.Nat.Order.Gappy public
open import Polynomial.Normal.Definition coeffs public
open import Polynomial.Normal.Construction coeffs public
open import Polynomial.Normal.Operations coeffs public
open import Polynomial.Normal.Semantics homo public
