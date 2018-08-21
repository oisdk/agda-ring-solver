{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

module Polynomials.Ring.Homomorphism.Lemmas
  {r₁ r₂ r₃ r₄}
  (coeff : RawRing r₁)
  (Zero-C : Pred (RawRing.Carrier coeff) r₂)
  (zero-c? : Decidable Zero-C)
  (ring : AlmostCommutativeRing r₃ r₄)
  (morphism : coeff -Raw-AlmostCommutative⟶ ring)
  (Zero-C⟶Zero-R : ∀ x → Zero-C x → AlmostCommutativeRing._≈_ ring (_-Raw-AlmostCommutative⟶_.⟦_⟧ morphism x) (AlmostCommutativeRing.0# ring))
  where

open AlmostCommutativeRing ring hiding (zero)
open import Polynomials.Ring.Reasoning ring
open import Polynomials.Ring.Normal coeff Zero-C zero-c?
open import Polynomials.Ring.Semantics coeff Zero-C zero-c? ring morphism
open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧ᵣ)
module Raw = RawRing coeff

open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product hiding (Σ)
import Data.Nat.Properties as ℕ-≡
import Relation.Binary.PropositionalEquality as ≡
open import Function
open import Data.List as List using (_∷_; [])
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Data.Product.Irrelevant
open import Level using (Lift; lower; lift)
open import Data.Fin as Fin using (Fin)

pow-add : ∀ x i j → x ^ i * x ^ j ≈ x ^ (i ℕ.+ j)
pow-add x zero j = *-identityˡ (x ^ j)
pow-add x (suc i) j =
  begin
    x ^ suc i * x ^ j
  ≡⟨⟩
    (x * x ^ i) * x ^ j
  ≈⟨ *-assoc x _ _ ⟩
    x * (x ^ i * x ^ j)
  ≈⟨ *≫ pow-add x i j ⟩
    x * x ^ (i ℕ.+ j)
  ≡⟨⟩
    x ^ suc (i ℕ.+ j)
  ∎

pow-hom : ∀ {n} i
        → (xs : Coeffs n)
        → (ρ : Carrier)
        → (Ρ : Vec Carrier n)
        → Σ⟦ xs ⟧ (ρ , Ρ) * ρ ^ i ≈ Σ⟦ xs ⍓ i ⟧ (ρ , Ρ)
pow-hom i [] ρ Ρ = zeroˡ (ρ ^ i)
pow-hom i (x Δ j ∷ xs) ρ Ρ = *-assoc _ (ρ ^ j) (ρ ^ i) ︔ *≫ pow-add ρ j i

zero-hom : ∀ {n} (p : Poly n) → Zero p → (Ρ : Vec Carrier n) → ⟦ p ⟧ Ρ ≈ 0#
zero-hom (Κ x  Π i≤n) p≡0 Ρ = Zero-C⟶Zero-R x p≡0
zero-hom (Σ (_ ∷ _) Π i≤n) (lift ())
zero-hom (Σ [] {()} Π i≤n) p≡0 Ρ

∷↓-hom : ∀ {n}
       → (x : Poly n)
       → (i : ℕ)
       → (xs : Coeffs n)
       → (ρ : Carrier)
       → (Ρ : Vec Carrier n)
       → Σ⟦ x ^ i ∷↓ xs ⟧ (ρ , Ρ) ≈ (⟦ x ⟧ Ρ + Σ⟦ xs ⟧ (ρ , Ρ) * ρ) * ρ ^ i
∷↓-hom x i xs ρ Ρ with zero? x
∷↓-hom x i xs ρ Ρ | no ¬p = refl
∷↓-hom x i xs ρ Ρ | yes p =
  begin
    Σ⟦ xs ⍓ suc i ⟧ (ρ , Ρ)
  ≈⟨ sym (pow-hom _ xs ρ Ρ) ⟩
    Σ⟦ xs ⟧ (ρ , Ρ) * ρ ^ (suc i)
  ≈⟨ sym (*-assoc _ ρ _) ⟩
    Σ⟦ xs ⟧ (ρ , Ρ) * ρ * ρ ^ i
  ≈⟨ ≪* (sym (+-identityˡ _) ︔ ≪+ sym (zero-hom x p _)) ⟩
    (⟦ x ⟧ Ρ + Σ⟦ xs ⟧ (ρ , Ρ) * ρ) * ρ ^ i
  ∎

Σ-Π↑-hom : ∀ {i n m}
         → (xs : Coeffs i)
         → (si≤n : suc i ≤ n)
         → (sn≤m : suc n ≤ m)
         → (Ρ : Vec Carrier m)
         → Σ⟦ xs ⟧ (drop-1 (≤-trans-pred si≤n sn≤m) Ρ)
         ≈ Σ⟦ xs ⟧ (drop-1 si≤n (proj₂ (drop-1 sn≤m Ρ)))
Σ-Π↑-hom xs si≤n m≤m (ρ ∷ Ρ) = refl
Σ-Π↑-hom xs si≤n (≤-s sn≤m) (_ ∷ Ρ) = Σ-Π↑-hom xs si≤n sn≤m Ρ

Π↑-hom : ∀ {n m}
       → (x : Poly n)
       → (sn≤m : suc n ≤ m)
       → (Ρ : Vec Carrier m)
       → ⟦ x Π↑ sn≤m ⟧ Ρ ≈ ⟦ x ⟧ (proj₂ (drop-1 sn≤m Ρ))
Π↑-hom (Κ x  Π i≤sn) sn≤m Ρ = refl
Π↑-hom (Σ xs Π i≤sn) sn≤m Ρ = Σ-Π↑-hom xs i≤sn sn≤m Ρ

Π↓-hom : ∀ {n m}
       → (xs : Coeffs n)
       → (sn≤m : suc n ≤ m)
       → (Ρ : Vec Carrier m)
       → ⟦ xs Π↓ sn≤m ⟧ Ρ ≈ Σ⟦ xs ⟧ (drop-1 sn≤m Ρ)
Π↓-hom []                       sn≤m Ρ = 0-homo
Π↓-hom (x₁   Δ zero  ∷ x₂ ∷ xs) sn≤m Ρ = refl
Π↓-hom (x    Δ suc j ∷ xs)      sn≤m Ρ = refl
Π↓-hom (_≠0 x {x≠0} Δ zero  ∷ []) sn≤m Ρ =
  let (ρ , Ρ′) = drop-1 sn≤m Ρ
  in
  begin
    ⟦ x Π↑ sn≤m ⟧ Ρ
  ≈⟨ Π↑-hom x sn≤m Ρ ⟩
    ⟦ x ⟧ Ρ′
  ≈⟨ sym (*-identityʳ _) ⟩
    ⟦ x ⟧ Ρ′ * 1#
  ≈⟨ ≪* sym (+-identityʳ _) ⟩
    (⟦ x ⟧ Ρ′ + 0#) * 1#
  ≈⟨ ≪* +≫ sym (zeroˡ ρ) ⟩
    (⟦ x ⟧ Ρ′ + 0# * ρ) * 1#
  ≡⟨⟩
    Σ⟦ _≠0 x {x≠0} Δ zero ∷ [] ⟧ (ρ , Ρ′)
  ∎

drop-1⇒lookup : ∀ {n}
              → (i : Fin n)
              → (Ρ : Vec Carrier n)
              → proj₁ (drop-1 (Fin⇒≤ i) Ρ) ≡.≡ Vec.lookup i Ρ
drop-1⇒lookup Fin.zero (ρ ∷ Ρ) = ≡.refl
drop-1⇒lookup (Fin.suc i) (ρ ∷ Ρ) = drop-1⇒lookup i Ρ


≤-space : ∀ {i n} → i ≤ n → ℕ
≤-space m≤m = zero
≤-space (≤-s x) = suc (≤-space x)

x∸x≡0 : ∀ x → x ℕ.∸ x ≡.≡ 0
x∸x≡0 zero = ≡.refl
x∸x≡0 (suc x) = x∸x≡0 x
open import Data.Empty
x≮0 : ∀ x → suc x ≤ 0 → ⊥
x≮0 x ()

≤-pred-both : ∀ i n → suc i ≤ suc n → i ≤ n
≤-pred-both i .i m≤m = m≤m
≤-pred-both i zero (≤-s x) = ⊥-elim (x≮0 _ x)
≤-pred-both i (suc n) (≤-s x) = ≤-s (≤-pred-both _ _ x)

lemma₂ : ∀ n i → i ≤ n → suc (n ℕ.∸ i) ≡.≡ suc n ℕ.∸ i
lemma₂ n zero prf = ≡.refl
lemma₂ zero (suc i) prf = ⊥-elim (x≮0 _ prf)
lemma₂ (suc n) (suc i) prf = lemma₂ n i (≤-pred-both _ _ prf)

≤-space≡- : ∀ i n → (x : i ≤ n) → ≤-space x ≡.≡ n ℕ.∸ i
≤-space≡- i n m≤m = ≡.sym (x∸x≡0 i)
≤-space≡- i n (≤-s x) = ≡.trans (≡.cong suc (≤-space≡- _ _ x)) (lemma₂ _ _ x)

vec-drop : (n : ℕ) → ∀ {m} → Vec Carrier m → Vec Carrier (m ℕ.∸ n)
vec-drop zero xs = xs
vec-drop (suc n) [] = []
vec-drop (suc n) (x ∷ xs) = vec-drop n xs
