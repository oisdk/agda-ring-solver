-- Another way to encode ≥, but where the induction *reduces* the size
-- of the smaller argument. This means it can be efficiently used to
-- encode the modular type.
module Data.Nat.Order.Smaller where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Empty
open import Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Sum as Sum using (inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)

infix 4 _≥_
-- When encoding a modular arithmetic type, the inductive structure
-- of this will mimic the peano number it's representing. In other
-- words:
--
--   m≥m = zero
--   s≥m = suc
data _≥_ (m : ℕ) : ℕ → Set where
  m≥m : m ≥ m
  s≥m : ∀ {n} → m ≥ suc n → m ≥ n

-- While this is a proof that anything is greater than zero, it will
-- also be used to represent the "nines" in the number system. (The
-- greatest digit, which is nine in base 10)
--
-- 𝒪(n)
m≥0 : ∀ {m} → m ≥ zero
m≥0 {m} = go _ m≥m
  where
  go : ∀ n → m ≥ n → m ≥ 0
  go zero m≥n = m≥n
  go (suc n) m≥n = go n (s≥m m≥n)

-- 𝒪(n)
toNat : ∀ {n m} → n ≥ m → ℕ
toNat m≥m = zero
toNat (s≥m prf) = suc (toNat prf)

0≯m : ∀ {m} → 0 ≥ suc m → ⊥
0≯m (s≥m 0>m) = 0≯m 0>m

-- 𝒪(n)
≥-suc : ∀ {n m} → n ≥ m → suc n ≥ suc m
≥-suc m≥m = m≥m
≥-suc (s≥m n≥m) = s≥m (≥-suc n≥m)

-- 𝒪(n)
≥-sucˡ : ∀ {n m} → n ≥ m → suc n ≥ m
≥-sucˡ = s≥m ∘ ≥-suc

-- 𝒪(n)
≥-pred : ∀ {n m} → suc n ≥ suc m → n ≥ m
≥-pred m≥m = m≥m
≥-pred (s≥m sn≥sm) = s≥m (≥-pred sn≥sm)

-- ≥-trans (x ≥ y) (y ≥ z)
-- 𝒪(y)
≥-trans : Transitive _≥_
≥-trans x≥y m≥m = x≥y
≥-trans x≥y (s≥m y≥z) = s≥m (≥-trans x≥y y≥z)

-- 𝒪(n)
n+m≥m : ∀ n m → n ℕ.+ m ≥ m
n+m≥m n _ = go n m≥m
  where
  go : ∀ {x} y {z} → x ≥ y ℕ.+ z → x ≥ z
  go zero x≥y+z = x≥y+z
  go (suc y) x≥y+z = go y (s≥m x≥y+z)

-- 𝒪(n²)
≥-total : Total _≥_
≥-total zero y = inj₂ m≥0
≥-total (suc x) zero = inj₁ m≥0
≥-total (suc x) (suc y) = Sum.map ≥-suc ≥-suc (≥-total x y)

infix 4 _>_
_>_ : ℕ → ℕ → Set
x > y = x ≥ suc y

-- 𝒪(n)
sm>0 : ∀ {m} → suc m > 0
sm>0 {m} = go _ m≥m
  where
  go : ∀ n → suc m ≥ suc n → suc m ≥ 1
  go zero sm≥sn = sm≥sn
  go (suc n) sm≥sn = go n (s≥m sm≥sn)

-- 𝒪(n²)
_>?_ : Decidable _>_
zero >? y = no 0≯m
suc x >? zero = yes sm>0
suc x >? suc y with x >? y
(suc x >? suc y) | yes p = yes (≥-suc p)
(suc x >? suc y) | no ¬p = no (¬p ∘ ≥-pred)

import Data.Nat.Properties as Prop

toNat-+ : ∀ {m n} → (x : m ≥ n) → m ≡ toNat x ℕ.+ n
toNat-+ m≥m = refl
toNat-+ (s≥m x) = toNat-+ x ⟨ trans ⟩ Prop.+-suc (toNat x) _

toNat-≥ : ∀ {n m} → (x : m ≥ n) → m ≥ toNat x
toNat-≥ {n} x = subst (λ y → y ≥ toNat x) (Prop.+-comm n (toNat x) ⟨ trans ⟩ sym (toNat-+ x))  (n+m≥m n (toNat x))
