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
open import Relation.Binary.PropositionalEquality
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
import Data.Empty.Irrelevant as Irrel

open import Data.Nat.Order.Smaller public using (_≥_; m≥m; s≥m; toNat; 0≯m; ≥-pred; m≥0; n+m≥m; toNat-≥)

Mod : ℕ → Set
Mod = ∃ ∘ _≥_

incr : ∀ {n} → Mod n → Mod n × Bool
incr (zero   , pr) = (_  , m≥m   ), true
incr (suc sp , pr) = (sp , s≥m pr), false

fromNat : ∀ {n} m → .(n≥m : n ≥ m) →  Σ[ n-m ∈ Mod n ] toNat (proj₂ n-m) ≡ m
fromNat zero n≥m = (_ , m≥m), refl
fromNat (suc m) n≥m with fromNat m (s≥m n≥m)
... | (suc s , p  ), x≡m  = (s , s≥m p), cong suc x≡m
... | (zero  , n≥0), refl = Irrel.⊥-elim (contra _ zero n≥0 n≥m)
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
-_ (m , n≥m) = proj₁ (fromNat m n≥m)

infix 4 _≟_
_≟_ : ∀ {n} (x y : Mod n) → Dec (x ≡ y)
_≟_ {p} (_ , p≥d₁) (_ , p≥d₂) = go p≥d₁ p≥d₂
  where
  go : ∀ {d₁} (p≥d₁ : p ≥ d₁) → ∀ {d₂} (p≥d₂ : p ≥ d₂) → Dec ((d₁ , p≥d₁) ≡ (d₂ , p≥d₂))
  go m≥m m≥m = yes refl
  go m≥m (s≥m p≥d₂) = no (λ ())
  go (s≥m p≥d₁) m≥m = no (λ ())
  go (s≥m p≥d₁) (s≥m p≥d₂) with go p≥d₁ p≥d₂
  go (s≥m p≥d₁) (s≥m .p≥d₁) | yes refl = yes refl
  go (s≥m p≥d₁) (s≥m p≥d₂) | no ¬p = no λ { refl → ¬p refl }

-- 𝒪(n)
infixl 6 _+_
_+_ : ∀ {p} (x y : Mod p) → Mod p × Bool
_+_ {p} (d₁ , p≥d₁) (d₂ , p≥d₂) = go d₁ p≥d₁ d₂ p≥d₂
  where
  go : ∀ d₁ → p ≥ d₁ → ∀ d₂ → p ≥ d₂ → Mod p × Bool
  go d₁ m≥m d₂ p≥d₂ = (d₂ , p≥d₂), false
  go d₁ (s≥m p≥d₁) zero p≥d₂ = (suc d₁ , p≥d₁), true
  go d₁ (s≥m p≥d₁) (suc d₂) p≥d₂ = go (suc d₁) p≥d₁ d₂ (s≥m p≥d₂)

-- 𝒪(n)
infixl 7 _*_
_*_ : ∀ {p} → (x y : Mod p) → Mod p × Mod p
_*_ {p} x (_ , y) = go (_ , m≥m) m≥m y (toNat-≥ y)
  where
  go : (s : Mod p)
     → ∀ {d₁} (c : p ≥ d₁)
     → ∀ {d₂} (y : p ≥ d₂)
     → .(l : d₁ ≥ toNat y)
     → Mod p × Mod p
  go s c m≥m _ = s , (_ , c)
  go s c (s≥m p≥d) l with x + s
  go s c (s≥m p≥d) l          | s′ , false = go s′ c p≥d (s≥m l)
  go s {suc d₁} c (s≥m p≥d) l | s′ , true  = go s′ (s≥m c) p≥d (≥-pred l)
  go s {zero}   c (s≥m p≥d) l | s′ , true  = Irrel.⊥-elim (0≯m l)

module Order {p : ℕ} where
  data _≤_ : Mod p → Mod p → Set where
    z≤m : ∀ {n} → (p , m≥m) ≤ n
    s≤s : ∀ {n′ m′ n m} → (suc n′ , n) ≤ (suc m′ , m) → (_ , s≥m n) ≤ (_ , s≥m m)

  _≤?_ : Decidable _≤_
  (d₁ , p≥d₁) ≤? (d₂ , p≥d₂) = go p≥d₁ p≥d₂
    where
    go : ∀ {d₁} → (p≥d₁ : p ≥ d₁) → ∀ {d₂} (p≥d₂ : p ≥ d₂) → Dec ((d₁ , p≥d₁) ≤ (d₂ , p≥d₂))
    go m≥m p≥d₂ = yes z≤m
    go (s≥m p≥d₁) m≥m = no λ ()
    go (s≥m p≥d₁) (s≥m p≥d₂) with go p≥d₁ p≥d₂
    go (s≥m p≥d₁) (s≥m p≥d₂) | yes p = yes (s≤s p)
    go (s≥m p≥d₁) (s≥m p≥d₂) | no ¬p = no λ { (s≤s x) → ¬p x }

  _<_ : Mod p → Mod p → Set
  (zero  , _  ) < _ = ⊥
  (suc d , p≥d) < y = (d , s≥m p≥d) ≤ y

  _<?_ : Decidable _<_
  (zero  , _  ) <? _ = no (λ z → z)
  (suc d , p≥d) <? y = (d , s≥m p≥d) ≤? y

