{-# OPTIONS --without-K --safe #-}

module EqBool where

open import Data.Bool

record HasEqBool {a} (A : Set a) : Set a where
  field _==_ : A → A → Bool

open HasEqBool ⦃ ... ⦄ public

open import Data.List as List using (List; _∷_; [])

==[] : ∀ {a} {A : Set a} → ⦃ _ : HasEqBool A ⦄ → List A → List A → Bool
==[] [] [] = true
==[] [] (x ∷ ys) = false
==[] (x ∷ xs) [] = false
==[] (x ∷ xs) (y ∷ ys) = x == y ∧ ==[] xs ys

instance
  eqList : ∀ {a} {A : Set a} → ⦃ _ : HasEqBool A ⦄ → HasEqBool (List A)
  _==_ ⦃ eqList ⦄ = ==[]

open import Data.Nat using (ℕ)
instance
  eqNat : HasEqBool ℕ
  _==_ ⦃ eqNat ⦄ = Agda.Builtin.Nat._==_
    where import Agda.Builtin.Nat

instance
  eqBool : HasEqBool Bool
  _==_ ⦃ eqBool ⦄ false false = true
  _==_ ⦃ eqBool ⦄ false true = false
  _==_ ⦃ eqBool ⦄ true y = y

open import Data.String using (String)
instance
  eqString : HasEqBool String
  _==_ ⦃ eqString ⦄ = Data.String.Unsafe._==_
    where import Data.String.Unsafe
