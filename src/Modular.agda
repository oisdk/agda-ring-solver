{-# OPTIONS --without-K #-}

module Modular where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Bool as Bool using (Bool; true; false)
open import Function
open import Data.Product
open import Data.Empty
open import Data.Unit using (⊤; tt)
open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)

import Data.Empty.Irrelevant as Irrel

module ≥ where
  infix 4 _≥_
  data _≥_ (m : ℕ) : ℕ → Set where
    m≥m : m ≥ m
    s≥m : ∀ {n} → m ≥ suc n → m ≥ n

  m≥0 : ∀ {m} → m ≥ zero
  m≥0 {m} = go _ m≥m
    where
    go : ∀ n → m ≥ n → m ≥ 0
    go zero m≥n = m≥n
    go (suc n) m≥n = go n (s≥m m≥n)

  toNat : ∀ {n m} → n ≥ m → ℕ
  toNat m≥m = zero
  toNat (s≥m prf) = suc (toNat prf)

  0≯m : ∀ {m} → 0 ≥ suc m → ⊥
  0≯m (s≥m 0>m) = 0≯m 0>m

  ≥-suc : ∀ {n m} → n ≥ m → suc n ≥ suc m
  ≥-suc m≥m = m≥m
  ≥-suc (s≥m n≥m) = s≥m (≥-suc n≥m)

  ≥-sucˡ : ∀ {n m} → n ≥ m → suc n ≥ m
  ≥-sucˡ = s≥m ∘ ≥-suc

  ≥-pred : ∀ {n m} → suc n ≥ suc m → n ≥ m
  ≥-pred m≥m = m≥m
  ≥-pred (s≥m sn≥sm) = s≥m (≥-pred sn≥sm)

  ≥-trans : Transitive _≥_
  ≥-trans x≥y m≥m = x≥y
  ≥-trans x≥y (s≥m y≥z) = s≥m (≥-trans x≥y y≥z)

  n+m≥m : ∀ n m → n ℕ.+ m ≥ m
  n+m≥m n _ = go n m≥m
    where
    go : ∀ {x} y {z} → x ≥ y ℕ.+ z → x ≥ z
    go zero x≥y+z = x≥y+z
    go (suc y) x≥y+z = go y (s≥m x≥y+z)

  ≥-total : Total _≥_
  ≥-total zero y = inj₂ m≥0
  ≥-total (suc x) zero = inj₁ m≥0
  ≥-total (suc x) (suc y) = Sum.map ≥-suc ≥-suc (≥-total x y)

  infix 4 _>_
  _>_ : ℕ → ℕ → Set
  x > y = x ≥ suc y

  sm>0 : ∀ {m} → suc m > 0
  sm>0 {m} = go _ m≥m
    where
    go : ∀ n → suc m ≥ suc n → suc m ≥ 1
    go zero sm≥sn = sm≥sn
    go (suc n) sm≥sn = go n (s≥m sm≥sn)

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

open ≥ using (_≥_; m≥m; s≥m; toNat; 0≯m; ≥-pred; m≥0; n+m≥m; toNat-≥)

record Mod (p : ℕ) : Set where
  constructor [_∣_]
  field
    d   : ℕ
    p≥d : p ≥ d
open Mod

incr : ∀ {n} → Mod n → Mod n × Bool
incr [ zero   ∣ pr ] = [ _  ∣ m≥m    ] , true
incr [ suc sp ∣ pr ] = [ sp ∣ s≥m pr ] , false

fromNat : ∀ {n} m → .(n≥m : n ≥ m) →  Σ[ n-m ∈ Mod n ] toNat (p≥d n-m) ≡ m
fromNat zero n≥m = [ _ ∣ m≥m ] , refl
fromNat (suc m) n≥m with fromNat m (s≥m n≥m)
... | [ suc s ∣ p   ] , x≡m  = [ s ∣ s≥m p ] , cong suc x≡m
... | [ zero  ∣ n≥0 ] , refl = Irrel.⊥-elim (contra _ zero n≥0 n≥m)
  where
  import Data.Nat.Properties as Prop

  n≱sk+n : ∀ n k {sk+n} → sk+n ≡ suc k ℕ.+ n → n ≥ sk+n → ⊥
  n≱sk+n n k wit (s≥m n≥sk+n) = n≱sk+n n (suc k) (cong suc wit) n≥sk+n
  n≱sk+n n k wit m≥m with Prop.+-cancelʳ-≡ 0 (suc k) wit
  ... | ()

  contra : ∀ n m → (n≥m : n ≥ m) → n ≥ suc (m ℕ.+ toNat n≥m) → ⊥
  contra n m m≥m n≥st = n≱sk+n n zero (cong suc (Prop.+-comm n 0)) n≥st
  contra n m (s≥m n≥m) n≥st = contra n (suc m) n≥m (subst (λ x → n ≥ suc x) (Prop.+-suc m (toNat n≥m)) n≥st)

-_ : ∀ {n} → Mod n → Mod n
-_ [ m ∣ n≥m ] = proj₁ (fromNat m n≥m)

module DecEq where
  open import Relation.Binary.PropositionalEquality renaming ([_] to ⟦_⟧)
  ≟-term : ∀ {i n} (x y : Mod n) → Reveal toNat · (p≥d x) is i → Dec (x ≡ y)
  ≟-term [ d₁ ∣ m≥m ] [ .d₁ ∣ m≥m ] _ = yes refl
  ≟-term [ d₁ ∣ m≥m ] [ d₂ ∣ s≥m p≥d₂ ] _ = no (λ ())
  ≟-term [ d₁ ∣ s≥m p≥d₁ ] [ d₂ ∣ m≥m ] _ = no (λ ())
  ≟-term [ d₁ ∣ s≥m p≥d₁ ] [ d₂ ∣ s≥m p≥d₂ ] ⟦ refl ⟧ with ≟-term [ suc d₁ ∣ p≥d₁ ] [ suc d₂ ∣ p≥d₂ ] ⟦ refl ⟧
  ≟-term [ d₁ ∣ s≥m p≥d₁ ] [ .d₁ ∣ s≥m .p≥d₁ ]  _ | yes refl = yes refl
  ≟-term [ d₁ ∣ s≥m p≥d₁ ] [ d₂ ∣ s≥m p≥d₂ ]  _  | no ¬p = no λ { refl → ¬p refl }

  infix 4 _≟_
  _≟_ : ∀ {n} (x y : Mod n) → Dec (x ≡ y)
  x ≟ y = ≟-term x y ⟦ refl ⟧
open DecEq public using (_≟_)

infixl 6 _+_
_+_ : ∀ {p} (x y : Mod p) → Mod p × Bool
_+_ {p} [ d₁ ∣ p≥d₁ ] [ d₂ ∣ p≥d₂ ] = go d₁ p≥d₁ d₂ p≥d₂
  where
  go : ∀ d₁ → p ≥ d₁ → ∀ d₂ → p ≥ d₂ → Mod p × Bool
  go d₁ m≥m d₂ p≥d₂ = [ d₂ ∣ p≥d₂ ] , false
  go d₁ (s≥m p≥d₁) zero p≥d₂ = [ suc d₁ ∣ p≥d₁ ] , true
  go d₁ (s≥m p≥d₁) (suc d₂) p≥d₂ = go (suc d₁) p≥d₁ d₂ (s≥m p≥d₂)

infixl 7 _*_
_*_ : ∀ {p} → (x y : Mod p) → Mod p × Mod p
_*_ {p} x [ _ ∣ y ] = go [ _ ∣ m≥m ] m≥m y (toNat-≥ y)
  where
  go : (s : Mod p)
     → ∀ {d₁} (c : p ≥ d₁)
     → ∀ {d₂} (y : p ≥ d₂)
     → .(l : d₁ ≥ toNat y)
     → Mod p × Mod p
  go s c m≥m _ = s , [ _ ∣ c ]
  go s c (s≥m p≥d) l with x + s
  go s c (s≥m p≥d) l          | s′ , false = go s′ c p≥d (s≥m l)
  go s {suc d₁} c (s≥m p≥d) l | s′ , true = go s′ (s≥m c) p≥d (≥-pred l)
  go s {zero}   c (s≥m p≥d) l | s′ , true = Irrel.⊥-elim (0≯m l)
