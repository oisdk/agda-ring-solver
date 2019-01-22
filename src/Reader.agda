module Reader where

-- The reader monad (mainly used for nice syntax with idiom brackets).

open import Level

Reader : ∀ {r a} → Set r → Set a → Set (a ⊔ r)
Reader R A = R → A

module _ {r} {R′ : Set r} where
  R : ∀ {a} → Set a → Set (a ⊔ r)
  R = Reader R′

  pure : ∀ {a} {A : Set a} → A → R A
  pure x = λ _ → x

  _<*>_ : ∀ {a b} {A : Set a} {B : Set b}
        → R (A → B) → R A → R B
  f <*> g = λ x → f x (g x)

  _>>=_ : ∀ {a b} {A : Set a} {B : Set b}
        → R A → (A → R B) → R B
  f >>= k = λ x → k (f x) x

