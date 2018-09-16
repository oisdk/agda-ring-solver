module Polynomials.Ring.Simple.Expr where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

infixl 6 _⊕_
infixl 7 _⊗_
data Expr  {ℓ} (A : Set ℓ) (n : ℕ) : Set ℓ where
  Κ : A → Expr A n
  Ι : Fin n → Expr A n
  _⊕_ : Expr A n → Expr A n → Expr A n
  _⊗_ : Expr A n → Expr A n → Expr A n
  ⊝_ : Expr A n → Expr A n
