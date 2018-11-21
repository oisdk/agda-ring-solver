{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing
open import Polynomial.Normal.Parameters
open import Data.List as List using (_∷_; []; foldr; List)
open import Function

module Polynomial.Homomorphism.Lemmas
  {r₁ r₂ r₃ r₄}
  (homo : Homomorphism r₁ r₂ r₃ r₄)
  where
open Homomorphism homo

open import Polynomial.Reasoning ring
open import Polynomial.Normal homo
open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero; compare)
open import Data.Product hiding (Σ)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Level using (Lift; lower; lift)
open import Data.Fin as Fin using (Fin)
open import Level using (_⊔_)

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
pow-hom i (x Δ j ∷ xs) ρ Ρ = *-assoc _ (ρ ^ j) (ρ ^ i) ︔ *≫ pow-add ρ j i

zero-hom : ∀ {n} (p : Poly n) → Zero p → (Ρ : Vec Carrier n) → ⟦ p ⟧ Ρ ≈ 0#
zero-hom (Κ x  Π i≤n) p≡0 Ρ = Zero-C⟶Zero-R x p≡0
zero-hom (Σ (_ ∷ _) Π i≤n) (lift ())
zero-hom (Σ [] {()} Π i≤n) p≡0 Ρ

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
  ≈⟨ ≪* (sym (+-identityˡ _) ︔ ≪+ sym (zero-hom x p _)) ⟩
    (⟦ x ⟧ Ρ + Σ⟦ xs ⟧ (ρ , Ρ) * ρ) * ρ ^ i
  ∎

-- norm-cons-hom : ∀ {n} x ρ (Ρ : Vec Carrier n) → Σ⟦ norm-cons x ⟧ (ρ , Ρ) ≈ (ρ , Ρ) ⟦∷⟧ x
-- norm-cons-hom (x Δ i , xs) ρ Ρ = ∷↓-hom x i xs ρ Ρ

Σ-Π↑-hom : ∀ {i n m}
         → (xs : Coeffs i)
         → (si≤n : suc i ≤′ n)
         → (sn≤m : suc n ≤′ m)
         → ∀ ρ
         → Σ⟦ xs ⟧ (drop-1 (≤′-step si≤n ⋈ sn≤m) ρ)
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

⋈-hom : ∀ {i j-1 n}
      → (i≤j-1 : i ≤′ j-1)
      → (j≤n   : suc j-1 ≤′ n)
      → (x : FlatPoly i)
      → ∀ ρ
      → ⟦ x Π i≤j-1 ⟧ (proj₂ (drop-1 j≤n ρ)) ≈ ⟦ x Π (≤′-step i≤j-1 ⋈ j≤n) ⟧ ρ
⋈-hom i≤j-1 j≤n (Κ x) _ = refl
⋈-hom i≤j-1 ≤′-refl (Σ x) (_ ∷ _) = refl
⋈-hom i≤j-1 (≤′-step j≤n) (Σ x {xn}) (_ ∷ ρ) = ⋈-hom i≤j-1 j≤n (Σ x {xn}) ρ

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

open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

drop-1⇒lookup : ∀ {n}
              → (i : Fin n)
              → (Ρ : Vec Carrier n)
              → proj₁ (drop-1 (Fin⇒≤ i) Ρ) ≡ Vec.lookup i Ρ
drop-1⇒lookup Fin.zero (ρ ∷ Ρ) = ≡.refl
drop-1⇒lookup (Fin.suc i) (ρ ∷ Ρ) = drop-1⇒lookup i Ρ

foldR : ∀ {a b p} {A : Set a} {B : Set b} (_R_ : B → List A → Set p)
           → {f : A → B → B}
           → {b : B}
           → (∀ y {ys zs} → ys R zs → f y ys R (y ∷ zs))
           → b R []
           → ∀ xs
           → foldr f b xs R xs
foldR _ f b [] = b
foldR P f b (x ∷ xs) = f x (foldR P f b xs)

poly-foldR : ∀ {n} ρ ρs
        → ([f] : Fold n)
        → (f : Carrier → Carrier)
        → (∀ x y → f x * y ≈ f (x * y))
        → (∀ y {ys} zs → Σ⟦ ys ⟧ (ρ , ρs) ≈ f (Σ⟦ zs ⟧ (ρ , ρs)) → [f] (y , ys) ⟦∷⟧ (ρ , ρs) ≈ f ((y , zs) ⟦∷⟧ (ρ , ρs)) )
        → (0# ≈ f 0#)
        → ∀ xs
        → Σ⟦ para [f] xs ⟧ (ρ , ρs) ≈ f (Σ⟦ xs ⟧ (ρ , ρs))
poly-foldR ρ Ρ f e dist step base [] = base
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

-- NOTES:
--
-- Useful laws:
--
-- * Third Homomorphism Theorem
--    If a function can be expressed as both foldl f₁ e and foldr f₂
--    e, then there is an associative f with unit e where
--    foldl f e == foldr f e == h
--    J. Gibbons. The Third Homomorphism Theorem. J. Functional Prog., Vol 6, No 4, 657–665, 1996.
--
-- * foldr-fusion
--    If g a ∘ h ≡ h ∘ f a
--    then
--    h ∘ foldr f z ≡ foldr g (h z)
--
-- * First duality
--    foldr ∙ b ≡ foldl ∙ b
--   (when ∙ is associative)
--
-- * Second duality:
--    foldr ⊕ e ≡ foldl ⊗ e
--    when
--    a ⊕ (b ⊗ c) ≡ (a ⊕ b) ⊗ c
--    a ⊕ e ≡ e ⊗ a

