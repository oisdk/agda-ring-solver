{-# OPTIONS --without-K --safe #-}

-- Polynomials over a commutative ring in sparse Horner normal form.
--
-- Much of the implementation is inspired by:
--
--   B. Grégoire and A. Mahboubi, ‘Proving Equalities in a Commutative
--   Ring Done Right in Coq’, in Theorem Proving in Higher Order
--   Logics, Berlin, Heidelberg, 2005, vol. 3603, pp. 98–113.
--
-- The main sources of efficience come from:
--
-- * Careful arrangement of operators to maintain *syntactic equality*.
--
-- * Avoiding of identities (like *1 or +0) with specialised data
--  structures.
open import Polynomial.Parameters

module Polynomial.NormalForm
  {c r₁ r₂ r₃}
  (homo : Homomorphism c r₁ r₂ r₃)
  where

open Homomorphism homo

-- The "injection index" is what allows us to store the nested
-- polynomials sparsely.
open import Polynomial.NormalForm.InjectionIndex public

-- The definition and types for the polynomial.
open import Polynomial.NormalForm.Definition coeffs public

-- Normalizing constructors.
open import Polynomial.NormalForm.Construction coeffs public

-- Definition of arithmetic operations etc.
open import Polynomial.NormalForm.Operations coeffs public

-- "Running" the polynomial on some input.
open import Polynomial.NormalForm.Semantics homo public
