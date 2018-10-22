{-# OPTIONS --without-K #-}

module Data.Stream where

open import Function
open import Data.Nat using (ℕ; suc; zero)
open import Data.List as List using (List; []; _∷_)
open import Data.Product as Product using (_×_; _,_)
open import Agda.Builtin.Size

infixr 5 _◂_
record Stream {i : Size} {a} (A : Set a) : Set a where
  coinductive
  constructor _◂_
  field
    head : A
    tail : ∀ {j : Size< i} → Stream {j} A
open Stream

pure : ∀ {a} {A : Set a} → A → Stream A
head (pure x) = x
tail (pure x) = pure x

_<*>_ : ∀ {i a b} {A : Set a} {B : Set b}
      → Stream {i} (A → B)
      → Stream {i} A
      → Stream {i} B
head (fs <*> xs) = head fs (head xs)
tail (fs <*> xs) = tail fs <*> tail xs

map : ∀ {i a b} {A : Set a} {B : Set b}
    → (A → B)
    → Stream {i} A
    → Stream {i} B
head (map f xs) = f (head xs)
tail (map f xs) = map f (tail xs)

_>>=_ : ∀ {i a b} {A : Set a} {B : Set b}
      → Stream {i} A
      → (A → Stream {i} B)
      → Stream {i} B
head (xs >>= f) = head (f (head xs))
tail (xs >>= f) = tail xs >>= (λ x → tail (f x))

_[_] : ∀ {a} {A : Set a}
     → Stream A
     → ℕ
     → A
xs [ zero  ] = head xs
xs [ suc i ] = tail xs [ i ]

take : ∀ {a} {A : Set a}
     → ℕ
     → Stream A
     → List A
take zero _ = []
take (suc n) xs = head xs ∷ take n (tail xs)

open import Data.Vec using (Vec; _∷_; [])
takeVec : ∀ {a} {A : Set a}
        → (n : ℕ)
        → Stream A
        → Vec A n
takeVec zero xs = []
takeVec (suc n) xs = head xs ∷ takeVec n (tail xs)

iterate : ∀ {a} {A : Set a}
        → (A → A)
        → A
        → Stream A
head (iterate f x) = x
tail (iterate f x) = iterate f (f x)

cycle : ∀ {a} {A : Set a}
      → A
      → List A
      → Stream A
cycle {A = A} x xs = go x xs
  where
  go : A → List A → Stream A
  head (go y ys) = y
  tail (go _ []) = go x xs
  tail (go _ (y ∷ ys)) = go y ys

unfoldr : ∀ {a b} {A : Set a} {B : Set b}
        → (B → A × B)
        → B
        → Stream A
unfoldr {A = A} {B = B} f b = go (f b)
  where
  go : A × B → Stream A
  head (go (x , _)) = x
  tail (go (_ , xs)) = go (f xs)

tails : ∀ {a} {A : Set a}
      → Stream A
      → Stream (Stream A)
head (tails xs) = xs
tail (tails xs) = tails (tail xs)

scanl : ∀ {i a b} {A : Set a} {B : Set b}
      → (B → A → B)
      → B
      → Stream {i} A
      → Stream {i} B
head (scanl f b xs) = b
tail (scanl f b xs) = scanl f (f b (head xs)) (tail xs)

mapAccumL : ∀ {i a b c} {A : Set a} {B : Set b} {C : Set c}
          → (A → B → C × A) → A → Stream {i} B → Stream {i} C
mapAccumL {A = A} {B = B} {C = C} f b xs = go (f b (head xs)) (tail xs)
  where
  go : ∀ {i} → C × A → (∀ {j : Size< i} → Stream {j} B) → Stream {i} C
  head (go (x , _) _) = x
  tail (go (_ , b) xs) = go (f b (head xs)) (tail xs)

record ⟪_⟫ {b} (B : Size → Set b) (i : Size) : Set b where
  coinductive
  field unbox : ∀ {j : Size< i} → B j
open ⟪_⟫ public

foldr : ∀ {a b} {A : Set a} (B : Size → Set b)
      → (∀ {j} → A → ⟪ B ⟫ j → B j)
      → ∀ {i}
      → Stream {i} A
      → B i
foldr {A = A} B f xs = f (head xs) (go (tail xs))
  where
  go : ∀ {i} → (∀ {j : Size< i} → Stream {j} A) → ⟪ B ⟫ i
  unbox (go xs) = f (head xs) (go (tail xs))

interleave : ∀ {i a} {A : Set a}
           → Stream {i} A
           → Stream {i} A
           → Stream {i} A
head (interleave xs ys) = head xs
tail (interleave xs ys) = interleave ys (tail xs)

interleave′ : ∀ {i a} {A : Set a}
            → Stream {i} A
            → (∀ {j : Size< i} → Stream {j} A)
            → Stream {i} A
head (interleave′ xs ys) = head xs
tail (interleave′ xs ys) = interleave′ ys (tail xs)

open Product.Σ

unzip : ∀ {i a b} {A : Set a} {B : Set b}
      → Stream {i} (A × B)
      → Stream {i} A × Stream {i} B
head (proj₁ (unzip xs)) = proj₁ (head xs)
tail (proj₁ (unzip xs)) = proj₁ (unzip (tail xs))
head (proj₂ (unzip xs)) = proj₂ (head xs)
tail (proj₂ (unzip xs)) = proj₂ (unzip (tail xs))

open import Relation.Binary

module Bisimulation {a ℓ} (setoid : Setoid a ℓ) where
  open Setoid setoid

  record _≋ₛ_ (xs ys : Stream Carrier) : Set ℓ where
    coinductive
    field
      head-≋ : head xs ≈ head ys
      tail-≋ : tail xs ≋ₛ tail ys
  open _≋ₛ_

  ≋ₛ-refl : ∀ {xs} → xs ≋ₛ xs
  head-≋ ≋ₛ-refl = refl
  tail-≋ ≋ₛ-refl = ≋ₛ-refl

  ≋ₛ-sym : ∀ {xs ys} → xs ≋ₛ ys → ys ≋ₛ xs
  head-≋ (≋ₛ-sym xs≋ys) = sym (head-≋ xs≋ys)
  tail-≋ (≋ₛ-sym xs≋ys) = ≋ₛ-sym (tail-≋ xs≋ys)

  ≋ₛ-trans : ∀ {xs ys zs} → xs ≋ₛ ys → ys ≋ₛ zs → xs ≋ₛ zs
  head-≋ (≋ₛ-trans xs≋ys ys≋zs) = trans (head-≋ xs≋ys) (head-≋ ys≋zs)
  tail-≋ (≋ₛ-trans xs≋ys ys≋zs) = ≋ₛ-trans (tail-≋ xs≋ys) (tail-≋ ys≋zs)

  open IsEquivalence

  ≋ₛ-setoid : Setoid a ℓ
  Carrier ≋ₛ-setoid = Stream Carrier
  _≈_ ≋ₛ-setoid = _≋ₛ_
  refl  (isEquivalence ≋ₛ-setoid) = ≋ₛ-refl
  sym   (isEquivalence ≋ₛ-setoid) = ≋ₛ-sym
  trans (isEquivalence ≋ₛ-setoid) = ≋ₛ-trans


