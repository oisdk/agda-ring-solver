module Induction.WellFounded.Syntax where

open import Data.Nat
open import Induction.Nat
open import Induction.WellFounded
open import Induction.WellFounded using (acc) public

⌊_⌋ : ℕ → Set
⌊_⌋ = Acc _<′_

⌊↓⌋ : ∀ {n} → ⌊ n ⌋
⌊↓⌋ {n} = <′-wellFounded n
