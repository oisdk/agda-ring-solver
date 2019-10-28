{-# OPTIONS --without-K --safe #-}

-- Definitions for the types of a polynomial stored in sparse horner
-- normal form.
--
-- These definitions ensure that the polynomial is actually in fully
-- canonical form, with no trailing zeroes, etc.

open import Polynomial.Parameters

module Polynomial.NormalForm.Definition
  {a}
  (coeffs : RawCoeff a)
  where

open import Polynomial.NormalForm.InjectionIndex

open import Relation.Nullary using (¬_)
open import Level            using (_⊔_)
open import Data.Empty       using (⊥)
open import Data.Unit        using (⊤)
open import Data.Nat         using (ℕ; suc; zero)
open import Data.Bool        using (T)
open import Data.List.Kleene.Internal public

infixl 6 _Δ_
record PowInd {c} (C : Set c) : Set c where
  inductive
  constructor _Δ_
  field
    coeff : C
    pow   : ℕ
open PowInd public

open RawCoeff coeffs

mutual
  -- A Polynomial is indexed by the number of variables it contains.
  infixl 6 _Π_
  record Poly (n : ℕ) : Set a where
    inductive
    constructor _Π_
    field
      {i}  : ℕ
      flat : FlatPoly i
      i≤n  : i ≤′ n

  data FlatPoly : ℕ → Set a where
    Κ : Carrier → FlatPoly zero
    Σ : ∀ {n} → (xs : Coeff n ⁺) → .{xn : Norm xs} → FlatPoly (suc n)

  -- A list of coefficients, paired with the exponent *gap* from the
  -- preceding coefficient. In other words, to represent the
  -- polynomial:
  --
  --   3 + 2x² + 4x⁵ + 2x⁷
  --
  -- We write:
  --
  --   [(3,0),(2,1),(4,2),(2,1)]
  --
  -- Which can be thought of as a representation of the expression:
  --
  --   x⁰ * (3 + x * x¹ * (2 + x * x² * (4 + x * x¹ * (2 + x * 0))))
  --
  -- This is sparse Horner normal form.

  Coeff : ℕ → Set a
  Coeff n = PowInd (NonZero n)

  -- We disallow zeroes in the coefficient list. This condition alone
  -- is enough to ensure a unique representation for any polynomial.
  infixl 6 _≠0
  record NonZero (i : ℕ) : Set a where
    inductive
    constructor _≠0
    field
      poly : Poly i
      .{poly≠0} : ¬ Zero poly

  -- This predicate is used (in its negation) to ensure that no
  -- coefficient is zero, preventing any trailing zeroes.
  Zero : ∀ {n} → Poly n → Set
  Zero (Κ x Π _) = T (Zero-C x)
  Zero (Σ _ Π _) = ⊥

  -- This predicate is used to ensure that all polynomials are in
  -- normal form: if a particular level is constant, than it can
  -- be collapsed into the level below it.
  Norm : ∀ {i} → Coeff i ⁺ → Set
  Norm (_ Δ zero  & [])    = ⊥
  Norm (_ Δ zero  & [ _ ]) = ⊤
  Norm (_ Δ suc _ & _)     = ⊤
open NonZero public
open Poly public
