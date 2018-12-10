{-# OPTIONS --without-K #-}

open import Polynomial.Parameters

module Polynomial.Homomorphism.Lemmas
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
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

open import Function

open Homomorphism homo
open import Polynomial.Reasoning ring
open import Polynomial.NormalForm homo

open import Polynomial.Exponentiation rawRing

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
        → ∀ ρ Ρ
        → Σ⟦ xs ⟧ (ρ , Ρ) * ρ ^ i ≈ Σ⟦ xs ⍓ i ⟧ (ρ , Ρ)
pow-hom i [] ρ Ρ = zeroˡ (ρ ^ i)
pow-hom i (x Δ j ∷ xs) ρ Ρ = *-assoc _ (ρ ^ j) (ρ ^ i) ⊙ *≫ pow-add ρ j i

pow-distrib : ∀ x y i
            → (x * y) ^ i ≈ x ^ i * y ^ i
pow-distrib x y ℕ.zero = sym (*-identityˡ _)
pow-distrib x y (suc i) =
  begin
    (x * y) * ((x * y) ^ i)
  ≈⟨ *≫ pow-distrib x y i ⟩
    (x * y) * (x ^ i * y ^ i)
  ≈⟨ *-assoc _ _ _ ⟨ trans ⟩ (*≫ *-comm _ _) ⟩
    x * ((x ^ i * y ^ i) * y)
  ≈⟨  (*≫ *-assoc _ _ _) ⟨ trans ⟩ sym (*-assoc _ _ _) ⟨ trans ⟩ (*≫ *-comm _ _) ⟩
    (x * x ^ i) * (y * y ^ i)
  ∎

pow-mult : ∀ x i j
         → (x ^ i) ^ j ≈ x ^ (j ℕ.* i)
pow-mult x i ℕ.zero = refl
pow-mult x i (suc j) =
  begin
    x ^ i * ((x ^ i) ^ j)
  ≈⟨ *≫ pow-mult x i j ⟩
    x ^ i * (x ^ (j ℕ.* i))
  ≈⟨ pow-add x i _ ⟩
    x ^ (i ℕ.+ j ℕ.* i)
  ∎

pow-cong : ∀ {x y} i → x ≈ y → x ^ i ≈ y ^ i
pow-cong ℕ.zero x≈y = refl
pow-cong (suc i) x≈y = x≈y ⟨ *-cong ⟩ pow-cong i x≈y

zero-hom : ∀ {n} (p : Poly n) → Zero p → (Ρ : Vec Carrier n) → 0# ≈ ⟦ p ⟧ Ρ
zero-hom (Σ (_ ∷ _) Π i≤n) ()
zero-hom (Σ [] {()} Π i≤n) p≡0 Ρ
zero-hom (Κ x  Π i≤n) p≡0 Ρ with RawCoeff.zero-c? coeffs x
zero-hom (Κ x  Π i≤n) p≡0 Ρ | nothing = ⊥-elim p≡0
zero-hom (Κ x  Π i≤n) p≡0 Ρ | just prf = Zero-C⟶Zero-R prf

∷↓-hom : ∀ {n}
       → (x : Poly n)
       → ∀ i xs ρ Ρ
       → Σ⟦ x Δ i ∷↓ xs ⟧ (ρ , Ρ) ≈ ((x , xs) ⟦∷⟧ (ρ , Ρ)) * ρ ^ i
∷↓-hom x i xs ρ Ρ with zero? x
∷↓-hom x i xs ρ Ρ | no ¬p = refl
∷↓-hom x i xs ρ Ρ | yes p =
  begin
    Σ⟦ xs ⍓ suc i ⟧ (ρ , Ρ)
  ≈⟨ sym (pow-hom _ xs ρ Ρ) ⟩
    Σ⟦ xs ⟧ (ρ , Ρ) * ρ ^ (suc i)
  ≈⟨ sym (*-assoc _ ρ _) ⟩
    Σ⟦ xs ⟧ (ρ , Ρ) * ρ * ρ ^ i
  ≈⟨ ≪* (sym (+-identityˡ _) ⊙ ≪+ (zero-hom x p _)) ⟩
    (⟦ x ⟧ Ρ + Σ⟦ xs ⟧ (ρ , Ρ) * ρ) * ρ ^ i
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
    Σ⟦ _≠0 x {x≠0} Δ 0 ∷ [] ⟧ (ρ , Ρ′)
  ∎


drop-1⇒lookup : ∀ {n}
              → (i : Fin n)
              → (Ρ : Vec Carrier n)
              → proj₁ (drop-1 (Fin⇒≤ i) Ρ) ≡ Vec.lookup i Ρ
drop-1⇒lookup Fin.zero (ρ ∷ Ρ) = ≡.refl
drop-1⇒lookup (Fin.suc i) (ρ ∷ Ρ) = drop-1⇒lookup i Ρ

poly-foldR : ∀ {n} ρ ρs
        → ([f] : Fold n)
        → (f : Carrier → Carrier)
        → (∀ x y → f x * y ≈ f (x * y))
        → (∀ y {ys} zs → Σ⟦ ys ⟧ (ρ , ρs) ≈ f (Σ⟦ zs ⟧ (ρ , ρs)) → [f] (y , ys) ⟦∷⟧ (ρ , ρs) ≈ f ((y , zs) ⟦∷⟧ (ρ , ρs)) )
        → (f 0# ≈ 0#)
        → ∀ xs
        → Σ⟦ para [f] xs ⟧ (ρ , ρs) ≈ f (Σ⟦ xs ⟧ (ρ , ρs))
poly-foldR ρ Ρ f e dist step base [] = sym base
poly-foldR ρ Ρ f e dist step base (x ≠0 Δ i ∷ xs) =
  let ys = para f xs
      y,zs = f (x , ys)
      y = proj₁ y,zs
      zs = proj₂ y,zs
  in
  begin
    Σ⟦ y Δ i ∷↓ zs ⟧ (ρ , Ρ)
  ≈⟨ ∷↓-hom y i zs ρ Ρ ⟩
    (y , zs) ⟦∷⟧ (ρ , Ρ) * ρ ^ i
  ≈⟨ ≪* step x xs (poly-foldR ρ Ρ f e dist step base xs) ⟩
    e ((x , xs) ⟦∷⟧ (ρ , Ρ)) * ρ ^ i
  ≈⟨ dist _ (ρ ^ i) ⟩
    e ((x , xs) ⟦∷⟧ (ρ , Ρ) * ρ ^ i)
  ∎

poly-mapR : ∀ {n} ρ Ρ
          → ([f] : Poly n → Poly n)
          → (f : Carrier → Carrier)
          → (∀ x y → f x * y ≈ f (x * y))
          → (∀ x y → f (x + y) ≈ f x + f y)
          → (∀ y → ⟦ [f] y ⟧ Ρ ≈ f (⟦ y ⟧ Ρ) )
          → (f 0# ≈ 0#)
          → ∀ xs
          → Σ⟦ poly-map [f] xs ⟧ (ρ , Ρ) ≈ f (Σ⟦ xs ⟧ (ρ , Ρ))
poly-mapR ρ ρs [f] f *-dist +-dist step′ base xs = poly-foldR ρ ρs (map₁ [f]) f *-dist step base xs
  where
  step = λ y {ys} zs ys≋zs →
    begin
      map₁ [f] (y , ys) ⟦∷⟧ (ρ , ρs)
    ≡⟨⟩
      ⟦ [f] y ⟧ ρs + Σ⟦ ys ⟧ (ρ , ρs) * ρ
    ≈⟨ step′ y ⟨ +-cong ⟩ (≪* ys≋zs ⊙ (*-dist _ ρ)) ⟩
      f (⟦ y ⟧ ρs) + f (Σ⟦ zs ⟧ (ρ , ρs) * ρ)
    ≈⟨ sym (+-dist _ _) ⟩
      f ((y , zs) ⟦∷⟧ (ρ , ρs))
    ∎
