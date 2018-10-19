{-# OPTIONS --without-K #-}

module Modular where

open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Bool

data _≤_ : ℕ → ℕ → Set where
  m≤m : ∀ {n} → n ≤ n
  s≤m : ∀ {m n} → suc m ≤ n → m ≤ n

record Mod (n : ℕ) : Set where
  constructor [_+_]
  field
    space : ℕ
    proof : space ≤ n

open import Data.Product

incr : ∀ {n} → Mod n → Mod n × Bool
incr [ zero   + pr ] = [ _  + m≤m    ] , true
incr [ suc sp + pr ] = [ sp + s≤m pr ] , false
