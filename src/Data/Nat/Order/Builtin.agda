module Data.Nat.Order.Builtin where

open import Data.Nat as ℕ using (ℕ; suc; zero; Ordering; less; equal; greater)
open import Agda.Builtin.Nat using (_-_; _<_; _==_; _+_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
import Relation.Binary.PropositionalEquality.TrustMe as TrustMe

less-hom : ∀ n m → ((n < m) ≡ true) → m ≡ suc (n + (m - n - 1))
less-hom zero zero ()
less-hom zero (suc m) _ = refl
less-hom (suc n) zero ()
less-hom (suc n) (suc m) n<m = cong suc (less-hom n m n<m)

eq-hom : ∀ n m → ((n == m) ≡ true) → n ≡ m
eq-hom zero zero _ = refl
eq-hom zero (suc m) ()
eq-hom (suc n) zero ()
eq-hom (suc n) (suc m) n≡m = cong suc (eq-hom n m n≡m)

gt-hom : ∀ n m → ((n < m) ≡ false) → ((n == m) ≡ false) → n ≡ suc (m + (n - m - 1))
gt-hom zero zero n<m ()
gt-hom zero (suc m) () n≡m
gt-hom (suc n) zero n<m n≡m = refl
gt-hom (suc n) (suc m) n<m n≡m = cong suc (gt-hom n m n<m n≡m)

compare : (n m : ℕ) → Ordering n m
compare n m with n < m  | inspect (_<_ n) m
compare n m | true | [ n<m ] rewrite TrustMe.erase (less-hom n m n<m) = less n (m - n - 1)
compare n m | false | [ n≮m ] with n == m | inspect (_==_ n) m
compare n m | false | [ n≮m ] | true  | [ n≡m ] rewrite TrustMe.erase (eq-hom n m n≡m) = equal m
compare n m | false | [ n≮m ] | false | [ n≢m ] rewrite TrustMe.erase (gt-hom n m n≮m n≢m) = greater m (n - m - 1)
