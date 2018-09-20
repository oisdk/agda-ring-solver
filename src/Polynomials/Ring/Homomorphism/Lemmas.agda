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

open import Data.List as List using (List; _∷_; []; foldr)
open import Function

module _ {ℓ₁ ℓ₂} (setoid : Setoid ℓ₁ ℓ₂) where
  open Setoid setoid
  open import Relation.Binary.EqReasoning setoid

  foldr-fusion : ∀ {a b} {A : Set a} {B : Set b}
               → (h : B → Carrier) {f : A → B → B} {g : A → Carrier → Carrier} (e : B)
               → (∀ x y z → y ≈ z → g x y ≈ g x z)
               → (∀ x y → h (f x y) ≈ g x (h y))
               → ∀ xs → h (foldr f e xs) ≈ foldr g (h e) xs
  foldr-fusion h {f} {g} e _ fuse [] = refl
  foldr-fusion h {f} {g} e cong fuse (x ∷ xs) =
    begin
      h (f x (foldr f e xs))
    ≈⟨ fuse x _ ⟩
      g x (h (foldr f e xs))
    ≈⟨ cong x _ _ (foldr-fusion h e cong fuse xs) ⟩
      g x (foldr g (h e) xs)
    ∎

module AOPA where
  open import Level
  open import Data.Product
  open import Data.List

  _←_ : ∀ {i j k} → Set i → Set j → Set (suc k ⊔ (j ⊔ i))
  _←_ {i} {j} {k} B A = B → A → Set k

  _←_⊣_ :  ∀ {i j} → Set i → Set j → (k : Level) → Set (suc k ⊔ (j ⊔ i))
  B  ← A ⊣ k = _←_ {k = k} B A

  ℙ : ∀ {ℓ} → Set ℓ → Set (suc ℓ)
  ℙ {ℓ} A = A → Set ℓ

  ∈ : ∀ {i} {A : Set i} → (A ← ℙ A)
  ∈ a s = s a

  _₁∘_ : ∀ {i j k l} {A : Set i} {B : Set j} {C : Set k} → (C ← B ⊣ l) → (A → B) → (C ← A)
  (R ₁∘ S) c a = R c (S a)

  foldr₁ : {A : Set} → {PB : Set1} → ((A × PB) → PB) → PB → List A → PB
  foldr₁ f e []      = e
  foldr₁ f e (a ∷ x) = f (a , foldr₁ f e x)

  Λ :  ∀ {i j} {A : Set i} {B : Set j} → (B ← A) → A → ℙ B
  Λ R a = λ b → R b a

  infixr 8 _·_
  infixr 9 _○_ _₁∘_

  _·_ : {A B : Set} → (B ← A) → ℙ A → ℙ B
  (R · s)  b = ∃ (λ a → (s a × R b a))

  _○_ : ∀ {i j k l m} {A : Set i}{B : Set j}{C : Set k} → (C ← B ⊣ l) → (B ← A ⊣ m) → (C ← A ⊣ (j ⊔ l ⊔ m))
  (R ○ S) c a = ∃ (λ b → S b a × R c b)

  open import Relation.Binary.PropositionalEquality

  fun : ∀ {i j} {A : Set i} {B : Set j} → (A → B) → (B ← A)
  fun f b a = f a ≡ b

  idR : ∀ {i} {A : Set i} → A ← A
  idR = fun id

  infixr 2 _⨉_

  _⨉_ : ∀ {i j k l m n} {A : Set i} {B : Set j} {C : Set k} {D : Set l}
        → (B ← A ⊣ m) → (D ← C ⊣ n) → ((B × D) ← (A × C))
  (R ⨉ S) (b , d) (a , c) = (R b a × S d c)


  foldR : {A B : Set} → (B ← (A × B)) → ℙ B → (B ← List A)
  foldR R S = ∈ ₁∘ foldr₁ (Λ (R ○ (idR ⨉ ∈))) S

open AlmostCommutativeRing ring hiding (zero)
open import Polynomials.Ring.Reasoning ring
open import Polynomials.Ring.Normal coeff Zero-C zero-c?
open import Polynomials.Ring.Semantics coeff Zero-C zero-c? ring morphism
open _-Raw-AlmostCommutative⟶_ morphism renaming (⟦_⟧ to ⟦_⟧ᵣ)
module Raw = RawRing coeff
open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Product hiding (Σ)
open import Data.Vec as Vec using (Vec; _∷_; [])
open import Level using (Lift; lower; lift)
open import Data.Fin as Fin using (Fin)
open import Data.Nat.Order.Compare using (compare) public
open import Level using (_⊔_)
open import Relation.Binary.Lifted

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

pow-hom : ∀ {n}
        → (a : ⌊ n ⌋)
        → ∀ i
        → (xs : Coeffs n)
        → (ρ : Carrier)
        → (Ρ : Vec Carrier n)
        → ⌊ a ⌋Σ⟦ xs ⟧ (ρ , Ρ) * ρ ^ i ≈ ⌊ a ⌋Σ⟦ xs ⍓ i ⟧ (ρ , Ρ)
pow-hom a i [] ρ Ρ = zeroˡ (ρ ^ i)
pow-hom a i (x Δ j ∷ xs) ρ Ρ = *-assoc _ (ρ ^ j) (ρ ^ i) ︔ *≫ pow-add ρ j i

zero-hom : ∀ {n} (a : ⌊ n ⌋) → (p : Poly n) → Zero p → (Ρ : Vec Carrier n) → ⌊ a ⌋⟦ p ⟧ Ρ ≈ 0#
zero-hom _ (Κ x  Π i≤n) p≡0 Ρ = Zero-C⟶Zero-R x p≡0
zero-hom _ (Σ (_ ∷ _) Π i≤n) (lift ())
zero-hom _ (Σ [] {()} Π i≤n) p≡0 Ρ

∷↓-hom : ∀ {n}
       → (a : ⌊ n ⌋)
       → (x : Poly n)
       → (i : ℕ)
       → (xs : Coeffs n)
       → (ρ : Carrier)
       → (Ρ : Vec Carrier n)
       → ⌊ a ⌋Σ⟦ x ^ i ∷↓ xs ⟧ (ρ , Ρ) ≈ ⌊ a ⌋⟦ x δ i ∷ ⌊ a ⌋Σ⟦ xs ⟧ ⟧ (ρ , Ρ)
∷↓-hom a x i xs ρ Ρ with zero? x
∷↓-hom a x i xs ρ Ρ | no ¬p = refl
∷↓-hom a x i xs ρ Ρ | yes p =
  begin
    ⌊ a ⌋Σ⟦ xs ⍓ suc i ⟧ (ρ , Ρ)
  ≈⟨ sym (pow-hom a (suc i) xs ρ Ρ) ⟩
    ⌊ a ⌋Σ⟦ xs ⟧ (ρ , Ρ) * ρ ^ suc i
  ≈⟨ sym (*-assoc _ ρ _) ⟩
    ⌊ a ⌋Σ⟦ xs ⟧ (ρ , Ρ) * ρ * ρ ^ i
  ≈⟨ ≪* sym ((≪+ zero-hom a x p Ρ) ⟨ trans ⟩ +-identityˡ _) ⟩
    (⌊ a ⌋⟦ x ⟧ Ρ + ⌊ a ⌋Σ⟦ xs ⟧ (ρ , Ρ) * ρ) * ρ ^ i
  ∎

∷↓-cong : ∀ {n}
        → (a : ⌊ n ⌋)
        → (x : Poly n)
        → (i : ℕ)
        → (xs : Coeffs n)
        → (ys : Coeffs n)
        → (ρ : Carrier)
        → (Ρ : Vec Carrier n)
        → ⌊ a ⌋Σ⟦ xs ⟧(ρ , Ρ) ≈ ⌊ a ⌋Σ⟦ ys ⟧(ρ , Ρ)
        → ⌊ a ⌋Σ⟦ x ^ i ∷↓ xs ⟧(ρ , Ρ) ≈ ⌊ a ⌋Σ⟦ x ^ i ∷↓ ys ⟧(ρ , Ρ)
∷↓-cong a x i xs ys ρ Ρ prf = ∷↓-hom x i xs ρ Ρ ︔ ≪* +≫ ≪* prf ︔ sym (∷↓-hom x i ys ρ Ρ)

Σ-Π↑-hom : ∀ {i n m}
         → (a : ⌊ i ⌋)
         → (xs : Coeffs i)
         → (si≤n : suc i ≤ n)
         → (sn≤m : suc n ≤ m)
         → (Ρ : Vec Carrier m)
         → ⌊ a ⌋Σ⟦ xs ⟧ (drop-1 (≤-s si≤n ⋈ sn≤m) Ρ)
         ≈ ⌊ a ⌋Σ⟦ xs ⟧ (drop-1 si≤n (proj₂ (drop-1 sn≤m Ρ)))
Σ-Π↑-hom xs si≤n m≤m (ρ ∷ Ρ) = refl
Σ-Π↑-hom xs si≤n (≤-s sn≤m) (_ ∷ Ρ) = Σ-Π↑-hom xs si≤n sn≤m Ρ

Π↑-hom : ∀ {n m}
       → (x : Poly n)
       → (sn≤m : suc n ≤ m)
       → (Ρ : Vec Carrier m)
       → ⟦ x Π↑ sn≤m ⟧ Ρ ≈ ⟦ x ⟧ (proj₂ (drop-1 sn≤m Ρ))
Π↑-hom (Κ x  Π i≤sn) sn≤m Ρ = refl
Π↑-hom (Σ xs Π i≤sn) sn≤m Ρ = Σ-Π↑-hom xs i≤sn sn≤m Ρ

⋈-hom : ∀ {i j-1 n}
      → (i≤j-1 : i ≤ j-1)
      → (j≤n   : suc j-1 ≤ n)
      → (x : FlatPoly i)
      → (Ρ : Vec Carrier n)
      → ⟦ x Π i≤j-1 ⟧ (proj₂ (drop-1 j≤n Ρ)) ≈ ⟦ x Π (≤-s i≤j-1 ⋈ j≤n) ⟧ Ρ
⋈-hom i≤j-1 j≤n (Κ x) Ρ = refl
⋈-hom i≤j-1 m≤m (Σ x) (ρ ∷ Ρ) = refl
⋈-hom i≤j-1 (≤-s j≤n) (Σ x {xn}) (ρ ∷ Ρ) = ⋈-hom i≤j-1 j≤n (Σ x {xn}) Ρ

Π↓-hom : ∀ {n m}
       → (xs : Coeffs n)
       → (sn≤m : suc n ≤ m)
       → (Ρ : Vec Carrier m)
       → ⟦ xs Π↓ sn≤m ⟧ Ρ ≈ ⌊ a ⌋Σ⟦ xs ⟧ (drop-1 sn≤m Ρ)
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
    ⌊ a ⌋Σ⟦ _≠0 x {x≠0} Δ zero ∷ [] ⟧ (ρ , Ρ′)
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

