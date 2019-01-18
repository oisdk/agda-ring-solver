{-# OPTIONS --without-K #-}

open import Polynomial.Parameters

module Polynomial.Homomorphism.Lemmas
  {r₁ r₂ r₃}
  (homo : Homomorphism r₁ r₂ r₃)
  where

open import Data.List                                  using (_∷_; [])
open import Relation.Nullary                           using (Dec; yes; no)
open import Data.Nat as ℕ                              using (ℕ; suc; zero; compare)
open import Data.Vec as Vec                            using (Vec; _∷_)
open import Level                                      using (lift)
open import Data.Fin                                   using (Fin)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)
open import Data.Product                               using (_,_; proj₁; proj₂; map₁)
open import Data.Empty                                 using (⊥-elim)
open import Data.Maybe                                 using (nothing; just)
open import Data.Bool using (Bool;true;false)
open import Data.Unit using (tt)
open import Function
import Data.Nat.Properties as ℕ-Prop

open Homomorphism homo
open import Polynomial.Reasoning ring
open import Polynomial.NormalForm homo

open import Polynomial.Exponentiation rawRing

pow-add′ : ∀ x i j → (x ^ i +1) * (x ^ j +1) ≈ x ^ (j ℕ.+ suc i) +1
pow-add′ x i ℕ.zero = refl
pow-add′ x i (suc j) =
  begin
    x ^ i +1 * (x ^ j +1 * x)
  ≈⟨ sym (*-assoc _ _ _) ⟩
    x ^ i +1 * x ^ j +1 * x
  ≈⟨ ≪* pow-add′ x i j ⟩
    x ^ (j ℕ.+ suc i) +1 * x
  ∎


pow-add : ∀ x y i j → y ^ j +1 * x *⟨ y ⟩^ i  ≈ x *⟨ y ⟩^ (i ℕ.+ suc j)
pow-add x y ℕ.zero j = refl
pow-add x y (suc i) j = go x y i j
  where
  go : ∀ x y i j → y ^ j +1 * ((y ^ i +1) * x) ≈ y ^ (i ℕ.+ suc j) +1 * x
  go x y ℕ.zero j =  sym (*-assoc _ _ _)
  go x y (suc i) j =
    begin
      y ^ j +1 * (y ^ i +1 * y * x)
    ≈⟨ *≫ *-assoc _ y x ⟩
      y ^ j +1 * (y ^ i +1 * (y * x))
    ≈⟨ go (y * x) y i j ⟩
      y ^ (i ℕ.+ suc j) +1 * (y * x)
    ≈⟨ sym (*-assoc _ y x) ⟩
      y ^ suc (i ℕ.+ suc j) +1 * x
    ∎

pow-opt : ∀ x ρ i → x *⟨ ρ ⟩^ i ≈ x * ρ ^ i
pow-opt x ρ ℕ.zero = sym (*-identityʳ x)
pow-opt x ρ (suc i) = *-comm _ _

pow-hom : ∀ {n} i
        → (xs : Coeffs n)
        → ∀ ρ ρs
        → Σ⟦ xs ⟧ (ρ , ρs) *⟨ ρ ⟩^ i ≈ Σ⟦ xs ⍓ i ⟧ (ρ , ρs)
pow-hom ℕ.zero [] ρ ρs = refl
pow-hom ℕ.zero (x Δ j ∷ xs) ρ ρs rewrite ℕ-Prop.+-identityʳ j = refl
pow-hom (suc i) [] ρ ρs = zeroʳ _
pow-hom (suc i) (x ≠0 Δ j ∷ xs) ρ ρs =
  begin
    ρ ^ i +1 * (((x , xs) ⟦∷⟧ (ρ , ρs)) *⟨ ρ ⟩^ j)
  ≈⟨ pow-add _ ρ j i ⟩
    (((x , xs) ⟦∷⟧ (ρ , ρs)) *⟨ ρ ⟩^ (j ℕ.+ suc i))
  ∎

pow-distrib-+1 : ∀ x y i → (x * y) ^ i +1 ≈ x ^ i +1 * y ^ i +1
pow-distrib-+1 x y ℕ.zero = refl
pow-distrib-+1 x y (suc i) =
  begin
    (x * y) ^ i +1 * (x * y)
  ≈⟨ ≪* pow-distrib-+1 x y i ⟩
    (x ^ i +1 * y ^ i +1) * (x * y)
  ≈⟨ *-assoc _ _ _ ⟨ trans ⟩ (*≫ (sym (*-assoc _ _ _) ⟨ trans ⟩ (≪* *-comm _ _))) ⟩
    x ^ i +1 * (x * y ^ i +1 * y)
  ≈⟨ (*≫ *-assoc _ _ _) ⟨ trans ⟩ sym (*-assoc _ _ _) ⟩
    (x ^ i +1 * x) * (y ^ i +1 * y)
  ∎

pow-distrib : ∀ x y i
            → (x * y) ^ i ≈ x ^ i * y ^ i
pow-distrib x y ℕ.zero = sym (*-identityˡ _)
pow-distrib x y (suc i) = pow-distrib-+1 x y i

pow-mult-+1 : ∀ x i j → (x ^ i +1) ^ j +1 ≈ x ^ (i ℕ.+ j ℕ.* suc i) +1
pow-mult-+1 x i ℕ.zero rewrite ℕ-Prop.+-identityʳ i = refl
pow-mult-+1 x i (suc j) =
  begin
    (x ^ i +1) ^ j +1 * (x ^ i +1)
  ≈⟨ ≪* pow-mult-+1 x i j ⟩
    (x ^ (i ℕ.+ j ℕ.* suc i) +1) * (x ^ i +1)
  ≈⟨ pow-add′ x _ i ⟩
    x ^ (i ℕ.+ suc (i ℕ.+ j ℕ.* suc i)) +1
  ∎

-- pow-mult : ∀ x i j
--          → (x ^ i) ^ j ≈ x ^ (j ℕ.* i)
-- pow-mult x i ℕ.zero = refl
-- pow-mult x i (suc j) = {!!}

pow-cong-+1 : ∀ {x y} i → x ≈ y → x ^ i +1 ≈ y ^ i +1
pow-cong-+1 ℕ.zero x≈y = x≈y
pow-cong-+1 (suc i) x≈y = pow-cong-+1 i x≈y ⟨ *-cong ⟩ x≈y

zero-hom : ∀ {n} (p : Poly n) → Zero p → (ρs : Vec Carrier n) → 0# ≈ ⟦ p ⟧ ρs
zero-hom (Σ (_ ∷ _) Π i≤n) ()
zero-hom (Σ [] {()} Π i≤n) p≡0 ρs
zero-hom (Κ x  Π i≤n) p≡0 ρs = Zero-C⟶Zero-R x p≡0

pow-suc : ∀ x i → x ^ suc i ≈ x * x ^ i
pow-suc x ℕ.zero = sym (*-identityʳ _)
pow-suc x (suc i) = *-comm _ _

pow-sucʳ : ∀ x i → x ^ suc i ≈ x ^ i * x
pow-sucʳ x ℕ.zero = sym (*-identityˡ _)
pow-sucʳ x (suc i) = refl

∷↓-hom : ∀ {n}
       → (x : Poly n)
       → ∀ i xs ρ ρs
       → Σ⟦ x Δ i ∷↓ xs ⟧ (ρ , ρs) ≈ ((x , xs) ⟦∷⟧ (ρ , ρs)) * ρ ^ i
∷↓-hom x i xs ρ ρs with zero? x
∷↓-hom x i xs ρ ρs | no ¬p = pow-opt _ ρ i
∷↓-hom x i xs ρ ρs | yes p =
  begin
    Σ⟦ xs ⍓ suc i ⟧ (ρ , ρs)
  ≈⟨ sym (pow-hom (suc i) xs ρ ρs) ⟩
    ρ ^ suc i * Σ⟦ xs ⟧ (ρ , ρs)
  ≈⟨ ≪* pow-suc ρ i ⟩
    ρ * ρ ^ i * Σ⟦ xs ⟧ (ρ , ρs)
  ≈⟨ (*-assoc _ _ _) ⟨ trans ⟩ (*≫ *-comm _ _) ⟨ trans ⟩ sym (*-assoc _ _ _)  ⟩
    (ρ * Σ⟦ xs ⟧ (ρ , ρs)) * ρ ^ i
  ≈⟨ ≪* sym ((+≫ sym (zero-hom x p ρs)) ⟨ trans ⟩ +-identityʳ _) ⟩
    (ρ * Σ⟦ xs ⟧ (ρ , ρs) + ⟦ x ⟧ ρs) * ρ ^ i
  ∎

Σ-Π↑-hom : ∀ {i n m}
         → (xs : Coeffs i)
         → (si≤n : suc i ≤′ n)
         → (sn≤m : suc n ≤′ m)
         → ∀ ρ
         → Σ⟦ xs ⟧ (drop-1 (≤′-step si≤n ⟨ ≤′-trans ⟩ sn≤m) ρ)
         ≈ Σ⟦ xs ⟧ (drop-1 si≤n (proj₂ (drop-1 sn≤m ρ)))
Σ-Π↑-hom xs si≤n ≤′-refl (_ ∷ _) = refl
Σ-Π↑-hom xs si≤n (≤′-step sn≤m) (_ ∷ ρ) = Σ-Π↑-hom xs si≤n sn≤m ρ

Π↑-hom : ∀ {n m}
       → (x : Poly n)
       → (sn≤m : suc n ≤′ m)
       → ∀ ρ
       → ⟦ x Π↑ sn≤m ⟧ ρ ≈ ⟦ x ⟧ (proj₂ (drop-1 sn≤m ρ))
Π↑-hom (Κ x  Π i≤sn) _ _ = refl
Π↑-hom (Σ xs Π i≤sn) = Σ-Π↑-hom xs i≤sn

trans-join-coeffs-hom : ∀ {i j-1 n}
                      → (i≤j-1 : suc i ≤′ j-1)
                      → (j≤n   : suc j-1 ≤′ n)
                      → (xs : Coeffs i)
                      → ∀ ρ
                      → Σ⟦ xs ⟧ (drop-1 i≤j-1 (proj₂ (drop-1 j≤n ρ))) ≈ Σ⟦ xs ⟧ (drop-1 (≤′-step i≤j-1 ⟨ ≤′-trans ⟩ j≤n) ρ)
trans-join-coeffs-hom i<j-1 ≤′-refl xs (_ ∷ _) = refl
trans-join-coeffs-hom i<j-1 (≤′-step j<n) xs (_ ∷ ρ) = trans-join-coeffs-hom i<j-1 j<n xs ρ

trans-join-hom : ∀ {i j-1 n}
      → (i≤j-1 : i ≤′ j-1)
      → (j≤n   : suc j-1 ≤′ n)
      → (x : FlatPoly i)
      → ∀ ρ
      → ⟦ x Π i≤j-1 ⟧ (proj₂ (drop-1 j≤n ρ)) ≈ ⟦ x Π (≤′-step i≤j-1 ⟨ ≤′-trans ⟩ j≤n) ⟧ ρ
trans-join-hom i≤j-1 j≤n (Κ x) _ = refl
trans-join-hom i≤j-1 j≤n (Σ x) = trans-join-coeffs-hom i≤j-1 j≤n x

Π↓-hom : ∀ {n m}
       → (xs : Coeffs n)
       → (sn≤m : suc n ≤′ m)
       → ∀ ρ
       → ⟦ xs Π↓ sn≤m ⟧ ρ ≈ Σ⟦ xs ⟧ (drop-1 sn≤m ρ)
Π↓-hom []                       sn≤m _ = 0-homo
Π↓-hom (x₁   Δ zero  ∷ x₂ ∷ xs) sn≤m _ = refl
Π↓-hom (x    Δ suc j ∷ xs)      sn≤m _ = refl
Π↓-hom (_≠0 x {x≠0} Δ zero  ∷ []) sn≤m ρs =
  let (ρ , ρs′) = drop-1 sn≤m ρs
  in
  begin
    ⟦ x Π↑ sn≤m ⟧ ρs
  ≈⟨ Π↑-hom x sn≤m ρs ⟩
    ⟦ x ⟧ ρs′
  ≈⟨ sym ((≪+ zeroʳ ρ) ⟨ trans ⟩ +-identityˡ _) ⟩
    ρ * 0# + ⟦ x ⟧ ρs′
  ∎

drop-1⇒lookup : ∀ {n}
              → (i : Fin n)
              → (ρs : Vec Carrier n)
              → proj₁ (drop-1 (Fin⇒≤ i) ρs) ≡ Vec.lookup i ρs
drop-1⇒lookup Fin.zero (ρ ∷ ρs) = ≡.refl
drop-1⇒lookup (Fin.suc i) (ρ ∷ ρs) = drop-1⇒lookup i ρs

poly-foldR : ∀ {n} ρ ρs
        → ([f] : Fold n)
        → (f : Carrier → Carrier)
        → (∀ x y → x * f y ≈ f (x * y))
        → (∀ y {ys} zs → Σ⟦ ys ⟧ (ρ , ρs) ≈ f (Σ⟦ zs ⟧ (ρ , ρs)) → [f] (y , ys) ⟦∷⟧ (ρ , ρs) ≈ f ((y , zs) ⟦∷⟧ (ρ , ρs)) )
        → (f 0# ≈ 0#)
        → ∀ xs
        → Σ⟦ para [f] xs ⟧ (ρ , ρs) ≈ f (Σ⟦ xs ⟧ (ρ , ρs))
poly-foldR ρ ρs f e dist step base [] = sym base
poly-foldR ρ ρs f e dist step base (x ≠0 Δ suc i ∷ xs) =
  let ys = para f xs
      y,zs = f (x , ys)
      y = proj₁ y,zs
      zs = proj₂ y,zs
  in
  begin
    Σ⟦ y Δ suc i ∷↓ zs ⟧ (ρ , ρs)
  ≈⟨ ∷↓-hom y (suc i) zs ρ ρs ⟩
    ((y , zs) ⟦∷⟧ (ρ , ρs)) * ρ ^ suc i
  ≈⟨ ≪* step x xs (poly-foldR ρ ρs f e dist step base xs) ⟩
    e ((x , xs) ⟦∷⟧ (ρ , ρs)) * (ρ ^ i +1)
  ≈⟨ *-comm _ _ ⟨ trans ⟩ dist _ _   ⟩
    e (ρ ^ i +1 * ((x , xs) ⟦∷⟧ (ρ , ρs)))
  ∎
poly-foldR ρ ρs f e dist step base (x ≠0 Δ ℕ.zero ∷ xs) =
  let ys = para f xs
      y,zs = f (x , ys)
      y = proj₁ y,zs
      zs = proj₂ y,zs
  in
  begin
    Σ⟦ y Δ ℕ.zero ∷↓ zs ⟧ (ρ , ρs)
  ≈⟨ ∷↓-hom y ℕ.zero zs ρ ρs ⟩
    ((y , zs) ⟦∷⟧ (ρ , ρs)) * ρ ^ ℕ.zero
  ≈⟨ ≪* step x xs (poly-foldR ρ ρs f e dist step base xs) ⟩
    e ((x , xs) ⟦∷⟧ (ρ , ρs)) * 1#
  ≈⟨ *-identityʳ _ ⟩
    e (((x , xs) ⟦∷⟧ (ρ , ρs)) )
  ∎

poly-mapR : ∀ {n} ρ ρs
          → ([f] : Poly n → Poly n)
          → (f : Carrier → Carrier)
          → (∀ x y → x * f y ≈ f (x * y))
          → (∀ x y → f (x + y) ≈ f x + f y)
          → (∀ y → ⟦ [f] y ⟧ ρs ≈ f (⟦ y ⟧ ρs) )
          → (f 0# ≈ 0#)
          → ∀ xs
          → Σ⟦ poly-map [f] xs ⟧ (ρ , ρs) ≈ f (Σ⟦ xs ⟧ (ρ , ρs))
poly-mapR ρ ρs [f] f *-dist +-dist step′ base xs = poly-foldR ρ ρs (map₁ [f]) f *-dist step base xs
  where
  step : ∀ y {ys} zs → Σ⟦ ys ⟧ (ρ , ρs) ≈ f (Σ⟦ zs ⟧ (ρ , ρs)) →(map₁ [f] (y , ys) ⟦∷⟧ (ρ , ρs)) ≈ f ((y , zs) ⟦∷⟧ (ρ , ρs))
  step y {ys} zs ys≋zs =
    begin
      map₁ [f] (y , ys) ⟦∷⟧ (ρ , ρs)
    ≡⟨⟩
      ρ * Σ⟦ ys ⟧ (ρ , ρs) + ⟦ [f] y ⟧ ρs
    ≈⟨ ((*≫ ys≋zs) ⟨ trans ⟩ *-dist ρ _) ⟨ +-cong ⟩ step′ y ⟩
      f (ρ * Σ⟦ zs ⟧ (ρ , ρs)) + f (⟦ y ⟧ ρs)
    ≈⟨ sym (+-dist _ _) ⟩
      f ((y , zs) ⟦∷⟧ (ρ , ρs))
    ∎
