{-# OPTIONS --without-K #-}

module Modular where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Bool

infix 4 _≥_
data _≥_ (m : ℕ) : ℕ → Set where
  m≥m : m ≥ m
  s≥m : ∀ {n} → m ≥ suc n → m ≥ n

record Mod (n : ℕ) : Set where
  constructor [_+_]
  field
    space : ℕ
    proof : n ≥ space

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

toNat′ : ∀ {m} → Mod m → ℕ
toNat′ [ _ + prf ] = toNat prf

open import Data.Empty

0≯m : ∀ {m} → 0 ≥ suc m → ⊥
0≯m (s≥m 0>m) = 0≯m 0>m

-- n+m≥m⇒ℕ≡m : ∀ n m → (n+m≥m : m ℕ.+ n ≥ m) → toNat n+m≥m ≡ n
-- n+m≥m⇒ℕ≡m .0 zero m≥m = refl
-- n+m≥m⇒ℕ≡m n zero (s≥m n+m≥m) = {!!}
-- n+m≥m⇒ℕ≡m n (suc m) n+m≥m = {!!}
--   where
--   prf : {!!}
--   prf = n+m≥m⇒ℕ≡m {!!} {!!} {!!}

-- fromNat : ∀ n m → (n≥m : n ≥ m) →  Σ[ x ∈ Mod n ] (toNat′ x ≡ m)
-- fromNat n zero n≥m = [ n + m≥m ] , refl
-- fromNat n (suc m) n≥m with fromNat n m (s≥m n≥m)
-- fromNat n (suc m) n≥m | [ zero + proof ] , snd = {!!}
-- fromNat n (suc m) n≥m | [ suc space + proof ] , snd = [ space + s≥m proof ] , cong suc snd

-- -- fromNat zero prf    = [ _ + m≥m ]
-- -- fromNat (suc n) prf with fromNat n (s≥m prf)
-- -- fromNat (suc n) prf | [ suc m + prf₂ ] = [ m + s≥m prf₂ ]
-- -- fromNat (suc n) prf | [ zero  + prf₂ ] = [ {!!} + {!!} ]
