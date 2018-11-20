{-# OPTIONS --without-K #-}

module Data.Nat.Order.Gappy where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat using () renaming (_≤′_ to _≤_; ≤′-refl to m≤m; ≤′-step to ≤-s) public

infixl 6 _⋈_
_⋈_ : ∀ {x y z} → x ≤ y → y ≤ z → x ≤ z
xs ⋈ m≤m = xs
xs ⋈ (≤-s ys) = ≤-s (xs ⋈ ys)

data Ordering {n : ℕ} : ∀ {i j}
                      → (i≤n : i ≤ n)
                      → (j≤n : j ≤ n)
                      → Set
                      where
  _<_ : ∀ {i j-1}
      → (i≤j-1 : i ≤ j-1)
      → (j≤n : suc j-1 ≤ n)
      → Ordering (≤-s i≤j-1 ⋈ j≤n) j≤n
  _>_ : ∀ {i-1 j}
      → (i≤n : suc i-1 ≤ n)
      → (j≤i-1 : j ≤ i-1)
      → Ordering i≤n (≤-s j≤i-1 ⋈ i≤n)
  eq : ∀ {i} → (i≤n : i ≤ n) → Ordering i≤n i≤n

_cmp_ : ∀ {i j n}
    → (x : i ≤ n)
    → (y : j ≤ n)
    → Ordering x y
m≤m cmp m≤m = eq m≤m
m≤m cmp ≤-s y = m≤m > y
≤-s x cmp m≤m = x < m≤m
≤-s x cmp ≤-s y with x cmp y
≤-s .(≤-s i≤j-1 ⋈ y) cmp ≤-s y                | i≤j-1 < .y = i≤j-1 < ≤-s y
≤-s x                cmp ≤-s .(≤-s j≤i-1 ⋈ x) | .x > j≤i-1 = ≤-s x > j≤i-1
≤-s x                cmp ≤-s .x               | eq .x = eq (≤-s x)

z≤n : ∀ {n} → zero ≤ n
z≤n {zero} = m≤m
z≤n {suc n} = ≤-s z≤n

open import Data.Fin as Fin using (Fin)

space : ∀ {n} → Fin n → ℕ
space f = suc (go f)
  where
  go : ∀ {n} → Fin n → ℕ
  go {suc n} Fin.zero = n
  go (Fin.suc x) = go x

Fin⇒≤ : ∀ {n} (x : Fin n) → space x ≤ n
Fin⇒≤ Fin.zero = m≤m
Fin⇒≤ (Fin.suc x) = ≤-s (Fin⇒≤ x)

module Properties where
  open import Relation.Binary
  open import Relation.Nullary
  open import Function

  ≤-trans : Transitive _≤_
  ≤-trans = _⋈_

  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
  s≤s m≤m = m≤m
  s≤s (≤-s x) = ≤-s (s≤s x)

  ≤-pred : ∀ {m n} → suc m ≤ n → m ≤ n
  ≤-pred m≤m = ≤-s m≤m
  ≤-pred (≤-s x) = ≤-s (≤-pred x)

  ≤-pred-both : ∀ {m n} → suc m ≤ suc n → m ≤ n
  ≤-pred-both m≤m = m≤m
  ≤-pred-both (≤-s x) = ≤-pred x

  _≤?_ : Decidable _≤_
  zero ≤? y = yes z≤n
  suc x ≤? zero = no (λ ())
  suc x ≤? suc y with x ≤? y
  (suc x ≤? suc y) | yes p = yes (s≤s p)
  (suc x ≤? suc y) | no ¬p = no (¬p ∘ ≤-pred-both)
