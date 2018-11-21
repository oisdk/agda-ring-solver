{-# OPTIONS --without-K #-}

module Data.Nat.Order.Gappy where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat using (_≤′_; ≤′-refl; ≤′-step; _<′_) public

infixl 6 _⋈_
_⋈_ : ∀ {x y z} → x ≤′ y → y ≤′ z → x ≤′ z
xs ⋈ ≤′-refl = xs
xs ⋈ (≤′-step ys) = ≤′-step (xs ⋈ ys)

data Ordering {n : ℕ} : ∀ {i j}
                      → (i≤n : i ≤′ n)
                      → (j≤n : j ≤′ n)
                      → Set
                      where
  lt : ∀ {i j-1}
     → (i≤j-1 : i ≤′ j-1)
     → (j≤n : suc j-1 ≤′ n)
     → Ordering (≤′-step i≤j-1 ⋈ j≤n) j≤n
  gt : ∀ {i-1 j}
     → (i≤n : suc i-1 ≤′ n)
     → (j≤i-1 : j ≤′ i-1)
     → Ordering i≤n (≤′-step j≤i-1 ⋈ i≤n)
  eq : ∀ {i} → (i≤n : i ≤′ n) → Ordering i≤n i≤n

_cmp_ : ∀ {i j n}
    → (x : i ≤′ n)
    → (y : j ≤′ n)
    → Ordering x y
≤′-refl cmp ≤′-refl = eq ≤′-refl
≤′-refl cmp ≤′-step y = gt ≤′-refl y
≤′-step x cmp ≤′-refl = lt x ≤′-refl
≤′-step x cmp ≤′-step y with x cmp y
≤′-step .(≤′-step i≤j-1 ⋈ y) cmp ≤′-step y                | lt i≤j-1 .y = lt i≤j-1 (≤′-step y)
≤′-step x                cmp ≤′-step .(≤′-step j≤i-1 ⋈ x) | gt .x j≤i-1 = gt (≤′-step x) j≤i-1
≤′-step x                cmp ≤′-step .x               | eq .x = eq (≤′-step x)

z≤n : ∀ {n} → zero ≤′ n
z≤n {zero} = ≤′-refl
z≤n {suc n} = ≤′-step z≤n

open import Data.Fin as Fin using (Fin)

space : ∀ {n} → Fin n → ℕ
space f = suc (go f)
  where
  go : ∀ {n} → Fin n → ℕ
  go {suc n} Fin.zero = n
  go (Fin.suc x) = go x

Fin⇒≤ : ∀ {n} (x : Fin n) → space x ≤′ n
Fin⇒≤ Fin.zero = ≤′-refl
Fin⇒≤ (Fin.suc x) = ≤′-step (Fin⇒≤ x)

module Properties where
  open import Relation.Binary
  open import Relation.Nullary
  open import Function

  ≤-trans : Transitive _≤′_
  ≤-trans = _⋈_

  s≤s : ∀ {m n} → m ≤′ n → suc m ≤′ suc n
  s≤s ≤′-refl = ≤′-refl
  s≤s (≤′-step x) = ≤′-step (s≤s x)

  ≤-pred : ∀ {m n} → suc m ≤′ n → m ≤′ n
  ≤-pred ≤′-refl = ≤′-step ≤′-refl
  ≤-pred (≤′-step x) = ≤′-step (≤-pred x)

  ≤-pred-both : ∀ {m n} → suc m ≤′ suc n → m ≤′ n
  ≤-pred-both ≤′-refl = ≤′-refl
  ≤-pred-both (≤′-step x) = ≤-pred x

  _≤?_ : Decidable _≤′_
  zero ≤? y = yes z≤n
  suc x ≤? zero = no (λ ())
  suc x ≤? suc y with x ≤? y
  (suc x ≤? suc y) | yes p = yes (s≤s p)
  (suc x ≤? suc y) | no ¬p = no (¬p ∘ ≤-pred-both)
