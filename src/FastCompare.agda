module FastCompare where

open import Agda.Builtin.Nat using (_<_; _==_; _+_)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.TrustMe
open import Data.Nat as ℕ using (ℕ; suc; zero; _∸_; Ordering; less; equal; greater)

lt-hom  : ∀ n m
  → ((n < m) ≡ true)
  → m ≡ suc (n + (m ∸ n ∸ 1))
lt-hom zero     zero     ()
lt-hom zero     (suc m)  _    = refl
lt-hom (suc n)  zero     ()
lt-hom (suc n)  (suc m)  n<m  =
  cong suc (lt-hom n m n<m)

eq-hom : ∀ n m
  → ((n == m) ≡ true)
  → n ≡ m
eq-hom zero      zero     _    = refl
eq-hom zero      (suc m)  ()
eq-hom (suc n)   zero     ()
eq-hom (suc n)   (suc m)  n≡m  =
  cong suc (eq-hom n m n≡m)

gt-hom : ∀ n m
  → ((n < m) ≡ false)
  → ((n == m) ≡ false)
  → n ≡ suc (m + (n ∸ m ∸ 1))
gt-hom zero       zero     n<m  ()
gt-hom zero       (suc m)  ()   n≡m
gt-hom (suc n)    zero     n<m  n≡m  = refl
gt-hom (suc n)    (suc m)  n<m  n≡m  =
  cong suc (gt-hom n m n<m n≡m)

compare : ∀ n m → Ordering n m
compare n m with n < m  | inspect (n <_) m
... | true  | [ n<m ] rewrite erase (lt-hom n m n<m)      = less n (m ∸ n ∸ 1)
... | false | [ n≮m ] with n == m | inspect (n ==_) m
... | true  | [ n≡m ] rewrite erase (eq-hom n m n≡m)      = equal m
... | false | [ n≢m ] rewrite erase (gt-hom n m n≮m n≢m) = greater m (n ∸ m ∸ 1)
