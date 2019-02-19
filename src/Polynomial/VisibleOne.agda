{-# OPTIONS --without-K --safe #-}

open import Polynomial.Parameters

module Polynomial.VisibleOne
  {a}
  (coeffs : RawCoeff a)
  where

-- This module provides a wrapper type for the coefficients of
-- a polynomial, which has the single purpose of avoiding
-- multiplying by 1.

data 1*x*1 : Set a where
  1* : 1*x*1
  ⟨_⟩ : RawCoeff.Carrier coeffs → 1*x*1
