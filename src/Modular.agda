{-# OPTIONS --without-K #-}

module Modular where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Bool

infix 4 _≥_
data _≥_ (m : ℕ) : ℕ → Set where
  m≥m : m ≥ m
  s≥m : ∀ {n} → m ≥ suc n → m ≥ n

record Mod (p : ℕ) : Set where
  constructor [_+_]
  field
    d   : ℕ
    p≥d : p ≥ d
open Mod

open import Data.Product

incr : ∀ {n} → Mod n → Mod n × Bool
incr [ zero   + pr ] = [ _  + m≥m    ] , true
incr [ suc sp + pr ] = [ sp + s≥m pr ] , false

m≥z : ∀ {m} → m ≥ zero
m≥z {m} = go _ m≥m
  where
  go : ∀ n → m ≥ n → m ≥ 0
  go zero m≥n = m≥n
  go (suc n) m≥n = go n (s≥m m≥n)

toNat : ∀ {n m} → n ≥ m → ℕ
toNat m≥m = zero
toNat (s≥m prf) = suc (toNat prf)

open import Data.Empty

0≯m : ∀ {m} → 0 ≥ suc m → ⊥
0≯m (s≥m 0>m) = 0≯m 0>m

open import Function
open import Relation.Binary.PropositionalEquality
import Data.Nat.Properties as Prop
import Data.Empty.Irrelevant as Irrel

n≢sk+n : ∀ k n → n ≡ suc (k ℕ.+ n) → ⊥
n≢sk+n k n wit with Prop.+-cancelʳ-≡ 0 (suc k) wit
... | ()

n≱sk+n : ∀ n k {sk+n} → sk+n ≡ suc k ℕ.+ n → n ≥ sk+n → ⊥
n≱sk+n n k wit m≥m = ⊥-elim (n≢sk+n k n wit)
n≱sk+n n k wit (s≥m n≥sk+n) = n≱sk+n n (suc k) (cong suc wit) n≥sk+n

toNat-contra : ∀ n m → (n≥m : n ≥ m) → n ≥ suc (m ℕ.+ toNat n≥m) → ⊥
toNat-contra n m m≥m n≥st = n≱sk+n n zero (cong suc (Prop.+-comm n 0)) n≥st
toNat-contra n m (s≥m n≥m) n≥st = toNat-contra n (suc m) n≥m (subst (λ x → n ≥ suc x) (Prop.+-suc m (toNat n≥m)) n≥st)

fromNat : ∀ {n} m → .(n≥m : n ≥ m) →  Σ[ x ∈ Mod n ] toNat (p≥d x) ≡ m
fromNat zero n≥m = [ _ + m≥m ] , refl
fromNat (suc m) n≥m with fromNat m (s≥m n≥m)
fromNat (suc .(toNat n≥0)) n≥m | [ zero + n≥0 ] , refl = Irrel.⊥-elim (toNat-contra _ zero n≥0 n≥m)
fromNat (suc m) n≥m | [ suc s + p ] , x≡m = [ s + s≥m p ] , cong suc x≡m
