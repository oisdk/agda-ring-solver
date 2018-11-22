open import Polynomial.Parameters

module Polynomial.NormalForm
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where

open Homomorphism homo
open import Polynomial.NormalForm.InjectionIndex public
open import Polynomial.NormalForm.Definition coeffs public
open import Polynomial.NormalForm.Construction coeffs public
open import Polynomial.NormalForm.Operations coeffs public
open import Polynomial.NormalForm.Semantics homo public
