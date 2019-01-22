module EqBool where

open import Data.Bool

record HasEqBool {a} (A : Set a) : Set a where
  field _==_ : A → A → Bool

open HasEqBool ⦃ ... ⦄ public

open import Data.List as List using (List; _∷_; [])
instance
  eqList : ∀ {a} {A : Set a} → ⦃ _ : HasEqBool A ⦄ → HasEqBool (List A)
  _==_ ⦃ eqList ⦄ [] [] = true
  _==_ ⦃ eqList ⦄ [] (x ∷ ys) = false
  _==_ ⦃ eqList ⦄ (x ∷ xs) [] = false
  _==_ ⦃ eqList ⦄ (x ∷ xs) (y ∷ ys) = x == y ∧ xs == ys

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
