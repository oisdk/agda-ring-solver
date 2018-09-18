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

_∺_ : ∀ {i j n}
    → (x : i ≤ n)
    → (y : j ≤ n)
    → Ordering x y
m≤m ∺ m≤m = eq m≤m
m≤m ∺ ≤-s y = m≤m > y
≤-s x ∺ m≤m = x < m≤m
≤-s x ∺ ≤-s y with x ∺ y
≤-s .(≤-s i≤j-1 ⋈ y) ∺ ≤-s y                | i≤j-1 < .y = i≤j-1 < ≤-s y
≤-s x                ∺ ≤-s .(≤-s j≤i-1 ⋈ x) | .x > j≤i-1 = ≤-s x > j≤i-1
≤-s x                ∺ ≤-s .x               | eq .x = eq (≤-s x)

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
