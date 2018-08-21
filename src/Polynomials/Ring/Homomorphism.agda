{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

----------------------------------------------------------------------
-- Homomorphism
----------------------------------------------------------------------
module Polynomials.Ring.Homomorphism
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

κ-hom : ∀ {n}
      → (x : Raw.Carrier)
      → (Ρ : Vec Carrier n)
      → ⟦ κ x ⟧ Ρ ≈ ⟦ x ⟧ᵣ
κ-hom x _ = refl

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
              → proj₁ (drop-1 (Fin⇒≤ i) Ρ) ≈ Vec.lookup i Ρ
drop-1⇒lookup Fin.zero (ρ ∷ Ρ) = refl
drop-1⇒lookup (Fin.suc i) (ρ ∷ Ρ) = drop-1⇒lookup i Ρ

ι-hom : ∀ {n} → (i : Fin n) → (Ρ : Vec Carrier n) → ⟦ ι i ⟧ Ρ ≈ Vec.lookup i Ρ
ι-hom i Ρ′ =
  let (ρ , Ρ) = drop-1 (Fin⇒≤ i) Ρ′
  in
  begin
    ⟦ (κ Raw.1# ^ 1 ∷↓ []) Π↓ Fin⇒≤ i ⟧ Ρ′
  ≈⟨ Π↓-hom (κ Raw.1# ^ 1 ∷↓ []) (Fin⇒≤ i) Ρ′ ⟩
    Σ⟦ κ Raw.1# ^ 1 ∷↓ [] ⟧ (ρ , Ρ)
  ≈⟨ ∷↓-hom (κ Raw.1#) 1 [] ρ Ρ  ⟩
    (⟦ κ Raw.1# ⟧ Ρ + Σ⟦ [] ⟧ (ρ , Ρ) * ρ) * ρ ^ 1
  ≡⟨⟩
    (⟦ Raw.1# ⟧ᵣ + 0# * ρ) * (ρ * 1#)
  ≈⟨ 1-homo ⟨ +-cong ⟩ zeroˡ ρ ⟨ *-cong ⟩ *-identityʳ ρ ⟩
    (1# + 0#) * ρ
  ≈⟨ ≪* +-identityʳ _ ⟩
    1# * ρ
  ≈⟨ *-identityˡ ρ ⟩
    ρ
  ≈⟨ drop-1⇒lookup i Ρ′ ⟩
    Vec.lookup i Ρ′
  ∎


-- mutual
--   ⊞-hom : ∀ {n}
--         → (xs : Poly n)
--         → (ys : Poly n)
--         → (Ρ : Vec Carrier n)
--         → ⟦ xs ⊞ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ + ⟦ ys ⟧ Ρ
--   ⊞-hom {ℕ.zero} xs ys [] = +-homo _ _
--   ⊞-hom {suc n} xs ys (ρ ∷ Ρ) = ⊞-coeffs-hom xs ys ρ Ρ

--   ⊞-coeffs-hom : ∀ {n}
--               → (xs : Coeffs n)
--               → (ys : Coeffs n)
--               → (ρ : Carrier)
--               → (Ρ : Vec Carrier n)
--               → ⟦ ⊞-coeffs xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ xs ⟧ (ρ ∷ Ρ) + ⟦ ys ⟧ (ρ ∷ Ρ)
--   ⊞-coeffs-hom [] ys ρ Ρ = sym (+-identityˡ (⟦ ys ⟧ (ρ ∷ Ρ)))
--   ⊞-coeffs-hom ((x , i) ∷ xs) = ⊞-ne-r-hom i x xs

--   ⊞-ne-hom : ∀ {n i j}
--            → (c : ℕ.Ordering i j)
--            → (x : Coeff n)
--            → (xs : Coeffs n)
--            → (y : Coeff n)
--            → (ys : Coeffs n)
--            → (ρ : Carrier)
--            → (Ρ : Vec Carrier n)
--            → ⟦ ⊞-ne c x xs y ys ⟧ (ρ ∷ Ρ)
--            ≈ ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
--   ⊞-ne-hom (ℕ.equal i) x xs y ys ρ Ρ =
--     let x′  = ⟦ proj₁~ x ⟧ Ρ
--         y′  = ⟦ proj₁~ y ⟧ Ρ
--         xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
--         ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
--     in
--     begin
--       ⟦ (proj₁~ x ⊞ proj₁~ y , i) ∷↓ xs ⊞ ys ⟧ (ρ ∷ Ρ)
--     ≈⟨ ∷↓-hom _ i (xs ⊞ ys) ρ Ρ ⟩
--       (⟦ proj₁~ x ⊞ proj₁~ y ⟧ Ρ + ⟦ xs ⊞ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
--     ≈⟨ ≪* begin
--             ⟦ proj₁~ x ⊞ proj₁~ y ⟧ Ρ + ⟦ xs ⊞ ys ⟧ (ρ ∷ Ρ) * ρ
--           ≈⟨ ⊞-hom (proj₁~ x) (proj₁~ y) Ρ ⟨ +-cong ⟩ (≪* ⊞-coeffs-hom xs ys ρ Ρ) ⟩
--             (x′ + y′) + (xs′ + ys′) * ρ
--           ≈⟨ +≫ distribʳ ρ _ _ ⟩
--             (x′ + y′) + (xs′ * ρ + ys′ * ρ)
--           ≈⟨ +-assoc x′ y′ _ ⟩
--             x′ + (y′ + (xs′ * ρ + ys′ * ρ))
--           ≈⟨ +≫ sym ( +-assoc y′ _ _ ) ⟩
--             x′ + ((y′ + xs′ * ρ) + ys′ * ρ)
--           ≈⟨ +≫ ≪+ +-comm y′ _ ⟩
--             x′ + ((xs′ * ρ + y′) + ys′ * ρ)
--           ≈⟨ +≫ +-assoc _ y′ _ ⟩
--             x′ + (xs′ * ρ + (y′ + ys′ * ρ))
--           ≈⟨ sym (+-assoc x′ _ _) ⟩
--             (x′ + xs′ * ρ) + (y′ + ys′ * ρ)
--           ∎ ⟩
--       ((x′ + xs′ * ρ) + (y′ + ys′ * ρ)) * ρ ^ i
--     ≈⟨ distribʳ (ρ ^ i) _ _ ⟩
--       (x′ + xs′ * ρ) * ρ ^ i + (y′ + ys′ * ρ) * ρ ^ i
--     ∎
--   ⊞-ne-hom (ℕ.less i k) x xs y ys ρ Ρ = ⊞-ne-r-step-hom i k y ys x xs ρ Ρ ︔ +-comm _ _
--   ⊞-ne-hom (ℕ.greater j k) = ⊞-ne-r-step-hom j k

--   ⊞-ne-r-step-hom : ∀ {n} j k
--                   → (x : Coeff n)
--                   → (xs : Coeffs n)
--                   → (y : Coeff n)
--                   → (ys : Coeffs n)
--                   → (ρ : Carrier)
--                   → (Ρ : Vec Carrier n)
--                   → ⟦ (y , j) ∷ ⊞-ne-r k x xs ys ⟧ (ρ ∷ Ρ)
--                   ≈ ⟦ (x , suc (j ℕ.+ k)) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
--   ⊞-ne-r-step-hom j k x xs y ys ρ Ρ =
--     let x′  = ⟦ proj₁~ x ⟧ Ρ
--         y′  = ⟦ proj₁~ y ⟧ Ρ
--         xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
--         ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
--     in
--     begin
--       (y′ + ⟦ ⊞-ne-r k x xs ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j
--     ≈⟨ ≪* +≫ ≪* ⊞-ne-r-hom k x xs ys ρ Ρ ⟩
--       (y′ + ((x′ + xs′ * ρ) * ρ ^ k + ys′) * ρ) * ρ ^ j
--     ≈⟨ ≪* +≫ distribʳ ρ _ _ ⟩
--       (y′ + ((x′ + xs′ * ρ) * ρ ^ k * ρ + ys′ * ρ)) * ρ ^ j
--     ≈⟨ ≪* (sym (+-assoc _ _ _) ︔ ≪+ +-comm _ _ ︔ +-assoc _ _ _) ⟩
--       ((x′ + xs′ * ρ) * ρ ^ k * ρ + (y′ + ys′ * ρ)) * ρ ^ j
--     ≈⟨ distribʳ (ρ ^ j) _ _ ⟩
--       (x′ + xs′ * ρ) * ρ ^ k * ρ * ρ ^ j + (y′ + ys′ * ρ) * ρ ^ j
--     ≈⟨ ≪+ begin
--              (((x′ + xs′ * ρ) * ρ ^ k) * ρ) * ρ ^ j
--            ≈⟨ *-assoc _ ρ (ρ ^ j) ⟩
--              ((x′ + xs′ * ρ) * ρ ^ k) * (ρ * ρ ^ j)
--            ≈⟨ *-assoc _ _ _ ⟩
--              (x′ + xs′ * ρ) * (ρ ^ k * (ρ * ρ ^ j))
--            ≈⟨ *≫ begin
--                     ρ ^ k * (ρ * ρ ^ j)
--                   ≈⟨ pow-add ρ k _ ⟩
--                     ρ ^ (k ℕ.+ suc j)
--                   ≡⟨ ≡.cong (ρ ^_) (ℕ-≡.+-comm k (suc j)) ⟩
--                     ρ ^ suc (j ℕ.+ k)
--                   ∎ ⟩
--              (x′ + xs′ * ρ) * ρ ^ suc (j ℕ.+ k)
--            ∎ ⟩
--       (x′ + xs′ * ρ) * ρ ^ suc (j ℕ.+ k) + (y′ + ys′ * ρ) * ρ ^ j
--     ≡⟨⟩
--       ⟦ (x , suc (j ℕ.+ k)) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ (y , j) ∷ ys ⟧ (ρ ∷ Ρ)
--     ∎

--   ⊞-ne-r-hom : ∀ {n} i
--              → (x : Coeff n)
--              → (xs : Coeffs n)
--              → (ys : Coeffs n)
--              → (ρ : Carrier)
--              → (Ρ : Vec Carrier n)
--              → ⟦ ⊞-ne-r i x xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ (x , i) ∷ xs ⟧ (ρ ∷ Ρ) + ⟦ ys ⟧ (ρ ∷ Ρ)
--   ⊞-ne-r-hom i x xs [] ρ Ρ = sym (+-identityʳ _)
--   ⊞-ne-r-hom i x xs ((y , j) ∷ ys) = ⊞-ne-hom (ℕ.compare i j) x xs y ys

-- mutual
--   ⊟-hom : ∀ {n}
--         → (xs : Poly n)
--         → (Ρ : Vec Carrier n)
--         → ⟦ ⊟ xs ⟧ Ρ ≈ - ⟦ xs ⟧ Ρ
--   ⊟-hom {ℕ.zero} xs [] = -‿homo _
--   ⊟-hom {suc _} xs (ρ ∷ Ρ) = ⊟-coeffs-hom xs ρ Ρ

--   ⊟-coeffs-hom : ∀ {n}
--               → (xs : Coeffs n)
--               → (ρ : Carrier)
--               → (Ρ : Vec Carrier n)
--               → ⟦ ⊟ xs ⟧ (ρ ∷ Ρ) ≈ - ⟦ xs ⟧ (ρ ∷ Ρ)
--   ⊟-coeffs-hom [] ρ Ρ =
--     begin
--       ⟦ ⊟ [] ⟧ (ρ ∷ Ρ)
--     ≡⟨⟩
--       0#
--     ≈⟨ sym (zeroʳ _) ⟩
--       - 0# * 0#
--     ≈⟨ -‿*-distribˡ 0# 0# ⟩
--       - (0# * 0#)
--     ≈⟨ -‿cong (zeroˡ 0#) ⟩
--       - 0#
--     ≡⟨⟩
--       - ⟦ [] ⟧ (ρ ∷ Ρ)
--     ∎
--   ⊟-coeffs-hom  ((x ,~ x≠0 , i) ∷ xs) ρ Ρ =
--     begin
--       ⟦ ⊟ ((x ,~ x≠0 , i) ∷ xs) ⟧ (ρ ∷ Ρ)
--     ≡⟨⟩
--       ⟦ (⊟ x , i) ∷↓ ⊟ xs ⟧ (ρ ∷ Ρ)
--     ≈⟨ ∷↓-hom (⊟ x) i (⊟ xs) ρ Ρ ⟩
--       (⟦ ⊟ x ⟧ Ρ + ⟦ ⊟ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
--     ≈⟨ ≪* (⊟-hom x Ρ ⟨ +-cong ⟩ (≪* ⊟-coeffs-hom xs ρ Ρ)) ⟩
--       (- ⟦ x ⟧ Ρ + - ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
--     ≈⟨ ≪* +≫ -‿*-distribˡ _ ρ ⟩
--       (- ⟦ x ⟧ Ρ + - (⟦ xs ⟧ (ρ ∷ Ρ) * ρ)) * ρ ^ i
--     ≈⟨ ≪* -‿+-comm _ _ ⟩
--       - (⟦ x ⟧ Ρ + ⟦ xs ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
--     ≈⟨ -‿*-distribˡ _ _ ⟩
--       - ⟦ (x ,~ x≠0 , i) ∷ xs ⟧ (ρ ∷ Ρ)
--     ∎

-- mutual
--   ⋊-hom : ∀ {n}
--         → (x : Poly n)
--         → (ys : Poly (suc n))
--         → (ρ : Carrier)
--         → (Ρ : Vec Carrier n)
--         → ⟦ x ⋊ ys ⟧ (ρ ∷ Ρ) ≈ ⟦ x ⟧ Ρ * ⟦ ys ⟧ (ρ ∷ Ρ)
--   ⋊-hom x [] ρ Ρ = sym (zeroʳ (⟦ x ⟧ Ρ))
--   ⋊-hom x ((y , j) ∷ ys) ρ Ρ =
--     let x′  = ⟦ x ⟧ Ρ
--         y′  = ⟦ proj₁~ y ⟧ Ρ
--         ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
--     in
--     begin
--       ⟦ x ⋊ ((y , j) ∷ ys) ⟧ (ρ ∷ Ρ)
--     ≡⟨⟩
--       ⟦ (x ⊠ proj₁~ y , j) ∷↓ x ⋊ ys ⟧ (ρ ∷ Ρ)
--     ≈⟨ ∷↓-hom _ j (x ⋊ ys) ρ Ρ ⟩
--       (⟦ x ⊠ proj₁~ y ⟧ Ρ + ⟦ x ⋊ ys ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ j
--     ≈⟨ ≪* (⊠-hom x _ Ρ ⟨ +-cong ⟩ (≪* ⋊-hom x ys ρ Ρ ︔ *-assoc _ _ _))⟩
--       (x′ * y′ + x′ * (ys′ * ρ)) * ρ ^ j
--     ≈⟨ ≪* sym (distribˡ x′ _ _ ) ⟩
--       x′ * (y′ + ys′ * ρ) * ρ ^ j
--     ≈⟨ *-assoc _ _ _ ⟩
--       x′ * ((y′ + ys′ * ρ) * ρ ^ j)
--     ∎

--   ⊠-hom : ∀ {n}
--         → (xs : Poly n)
--         → (ys : Poly n)
--         → (Ρ : Vec Carrier n)
--         → ⟦ xs ⊠ ys ⟧ Ρ ≈ ⟦ xs ⟧ Ρ * ⟦ ys ⟧ Ρ
--   ⊠-hom {ℕ.zero} xs ys [] = *-homo _ _
--   ⊠-hom {suc n} xs ys (ρ ∷ Ρ) = ⊠-coeffs-hom xs ys ρ Ρ

--   ⊠-step-hom : ∀ {n}
--              → (y : Poly n)
--              → (ys : Coeffs n)
--              → (xs : Coeffs n)
--              → (ρ : Carrier)
--              → (Ρ : Vec Carrier n)
--              → ⟦ List.foldr (⊠-step y ys) [] xs ⟧ (ρ ∷ Ρ)
--              ≈ ⟦ xs ⟧ (ρ ∷ Ρ) * (⟦ y ⟧ Ρ + ⟦ ys ⟧ (ρ ∷ Ρ) * ρ)
--   ⊠-step-hom y ys [] ρ Ρ = sym (zeroˡ _)
--   ⊠-step-hom y ys ((x ,~ x≠0 , i) ∷ xs) ρ Ρ =
--     let y′  = ⟦ y ⟧ Ρ
--         x′  = ⟦ x ⟧ Ρ
--         ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
--         xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
--         xs″ = List.foldr (⊠-step y ys) [] xs
--     in
--     begin
--       ⟦ (x ⊠ y , i) ∷↓ (x ⋊ ys ⊞ xs″) ⟧ (ρ ∷ Ρ)
--     ≈⟨  ∷↓-hom _ i _ ρ Ρ ⟩
--       (⟦ x ⊠ y ⟧ Ρ + ⟦ x ⋊ ys ⊞ xs″ ⟧ (ρ ∷ Ρ) * ρ) * ρ ^ i
--     ≈⟨ ≪* begin
--             ⟦ x ⊠ y ⟧ Ρ + ⟦ x ⋊ ys ⊞ xs″ ⟧ (ρ ∷ Ρ) * ρ
--           ≈⟨ ⊠-hom x y Ρ ⟨ +-cong ⟩ (≪* ⊞-hom (x ⋊ ys) _ (ρ ∷ Ρ)) ⟩
--             x′ * y′ + (⟦ x ⋊ ys ⟧ (ρ ∷ Ρ) + ⟦ xs″ ⟧ (ρ ∷ Ρ)) * ρ
--           ≈⟨ +≫ ≪* (⋊-hom x ys ρ Ρ ⟨ +-cong ⟩ ⊠-step-hom y ys xs ρ Ρ) ⟩
--             x′ * y′ + (x′ * ys′ + xs′ * (y′ + ys′ * ρ)) * ρ
--           ≈⟨ +≫ distribʳ ρ _ _ ⟩
--             x′ * y′ + (x′ * ys′ * ρ + xs′ * (y′ + ys′ * ρ) * ρ)
--           ≈⟨ sym (+-assoc _ _ _) ⟩
--             (x′ * y′ + x′ * ys′ * ρ) + xs′ * (y′ + ys′ * ρ) * ρ
--           ≈⟨ (+≫ *-assoc _ _ _ ︔ sym (distribˡ _ _ _)) ⟨ +-cong ⟩
--              (*-assoc _ _ _ ︔ *≫ *-comm _ _ ︔ sym (*-assoc _ _ _)) ⟩
--             x′ * (y′ + ys′ * ρ) + xs′ * ρ * (y′ + ys′ * ρ)
--           ≈⟨ sym (distribʳ _ _ _) ⟩
--             (x′ + xs′ * ρ) * (y′ + ys′ * ρ)
--           ∎
--      ⟩
--       (x′ + xs′ * ρ) * (y′ + ys′ * ρ) * ρ ^ i
--     ≈⟨ *-assoc _ _ _ ︔ *≫ *-comm _ _ ︔ sym (*-assoc _ _ _) ⟩
--       (x′ + xs′ * ρ) * ρ ^ i * (y′ + ys′ * ρ)
--     ∎

--   ⊠-coeffs-hom : ∀ {n}
--                → (xs : Coeffs n)
--                → (ys : Coeffs n)
--                → (ρ : Carrier)
--                → (Ρ : Vec Carrier n)
--                → ⟦ ⊠-coeffs xs ys ⟧ (ρ ∷ Ρ) ≈ ⟦ xs ⟧ (ρ ∷ Ρ) * ⟦ ys ⟧ (ρ ∷ Ρ)
--   ⊠-coeffs-hom xs [] ρ Ρ = sym (zeroʳ _)
--   ⊠-coeffs-hom xs ((y ,~ y≠0 , j) ∷ ys) ρ Ρ =
--     let xs′ = ⟦ xs ⟧ (ρ ∷ Ρ)
--         y′  = ⟦ y ⟧ Ρ
--         ys′ = ⟦ ys ⟧ (ρ ∷ Ρ)
--     in
--     begin
--       ⟦ List.foldr (⊠-step y ys) [] xs ⍓ j ⟧ (ρ ∷ Ρ)
--     ≈⟨ sym (pow-hom j (List.foldr (⊠-step y ys) [] xs) ρ Ρ) ⟩
--       ⟦ List.foldr (⊠-step y ys) [] xs ⟧ (ρ ∷ Ρ) * ρ ^ j
--     ≈⟨ ≪* ⊠-step-hom y ys xs ρ Ρ ⟩
--       xs′ * (y′ + ys′ * ρ) * ρ ^ j
--     ≈⟨ *-assoc _ _ _ ⟩
--       xs′ * ((y′ + ys′ * ρ) * ρ ^ j)
--     ≡⟨⟩
--       xs′ * ⟦ (y ,~ y≠0 , j) ∷ ys ⟧ (ρ ∷ Ρ)
--     ∎


