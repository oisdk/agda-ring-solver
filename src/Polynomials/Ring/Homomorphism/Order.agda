{-# OPTIONS --without-K #-}

open import Algebra
open import Relation.Binary hiding (Decidable)
open import Relation.Unary
open import Algebra.Solver.Ring.AlmostCommutativeRing

module Polynomials.Ring.Homomorphism.Order
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
import Data.Empty.Irrelevant as Irrelevant

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

≤-pred-both : ∀ {n i} → suc i ≤ suc n → i ≤ n
≤-pred-both m≤m = m≤m
≤-pred-both {zero} (≤-s ())
≤-pred-both {suc n} (≤-s x) = ≤-s (≤-pred-both x)

lemma₂ : ∀ n i → i ≤ n → suc (n ℕ.∸ i) ≡.≡ suc n ℕ.∸ i
lemma₂ n zero prf = ≡.refl
lemma₂ zero (suc i) ()
lemma₂ (suc n) (suc i) prf = lemma₂ n i (≤-pred-both prf)

≤-space≡- : ∀ {i n} → (x : i ≤ n) → ≤-space x ≡.≡ n ℕ.∸ i
≤-space≡- {i} m≤m = ≡.sym (x∸x≡0 i)
≤-space≡- (≤-s x) = ≡.trans (≡.cong suc (≤-space≡- x)) (lemma₂ _ _ x)

vec-drop : ∀ i {n} → Vec Carrier n → Vec Carrier (n ℕ.∸ i)
vec-drop zero xs = xs
vec-drop (suc n) [] = []
vec-drop (suc n) (x ∷ xs) = vec-drop n xs

data SpaceWitness {i : ℕ} : {n : ℕ} → (i ≤ n) → ℕ → Set where
  z-witness : SpaceWitness {i} m≤m zero
  s-witness : ∀ {n} {x : i ≤ n} {y : ℕ} → SpaceWitness {i} {n} x y → SpaceWitness {i} {suc n} (≤-s x) (suc y)

spaceWitness : ∀ {i n}
             → (x : i ≤ n)
             → SpaceWitness x (≤-space x)
spaceWitness m≤m = z-witness
spaceWitness (≤-s x) = s-witness (spaceWitness x)

vec-drop-space : ∀ {i n}
               → i ≤ n
               → Vec Carrier n
               → Vec Carrier i
vec-drop-space i≤n xs with spaceWitness i≤n
vec-drop-space .m≤m xs | z-witness = xs
vec-drop-space (≤-s i) (x ∷ xs) | s-witness res = vec-drop-space i xs

data Suffix : ℕ → Set r₃ where
  suffix : ∀ {n}
         → Vec Carrier n
         → ∀ i → Suffix (n ℕ.+ i)

open ≡

+-identity-no-k : ∀ x → x ℕ.+ 0 ≡ x
+-identity-no-k zero = ≡.refl
+-identity-no-k (suc x) = ≡.cong suc (+-identity-no-k x)

drop-suffix-to : ∀ i {n} → Vec Carrier n → Suffix i
drop-suffix-to i (x ∷ xs) with drop-suffix-to i xs
... | suffix ys zero = suffix ys zero
... | suffix ys (suc j) = ≡.subst Suffix (≡.sym (ℕ-≡.+-suc _ j)) (suffix (x ∷ ys) j)
drop-suffix-to i [] = suffix [] i

m≤k+m : ∀ m k → m ≤ k ℕ.+ m
m≤k+m m zero = m≤m
m≤k+m m (suc k) = ≤-s (m≤k+m m k)

m≤m+k : ∀ {m k} → m ≤ m ℕ.+ k
m≤m+k {m} {k} = ≡.subst (m ≤_) (ℕ-≡.+-comm k m) (m≤k+m m k)

-- open import Data.Empty

-- contra₁ : ∀ m k → suc (m ℕ.+ k) ≤ m → ⊥
-- contra₁ zero k ()
-- contra₁ (suc m) k prf = contra₁ m k (≤-pred-both prf)

-- contra₂ : ∀ m → suc m ≤ m → ⊥
-- contra₂ m = contra₁ m 0 ∘ ≡.subst (λ m′ → suc m′ ≤ m) (≡.sym (ℕ-≡.+-identityʳ _))

-- drop-irrel : ∀ i n
--            → .(i ≤ n)
--            → Vec Carrier n
--            → Vec Carrier i
-- drop-irrel i n i≤n xs with ℕ.compare i n
-- drop-irrel .m .(suc (m ℕ.+ k)) i≤n (x ∷ xs) | ℕ.less m k = drop-irrel _ _ m≤m+k xs
-- drop-irrel .m .m i≤n xs               | ℕ.equal m = xs
-- drop-irrel .(suc (m ℕ.+ k)) .m i≤n xs | ℕ.greater m k = Irrelevant.⊥-elim (contra₁ m k i≤n)

-- drop-irrel-lem₁ : ∀ i n
--                 → .(i≤sn : i ≤ suc n)
--                 → .(i≤n  : i ≤ n)
--                 → (x : Carrier)
--                 → (xs : Vec Carrier n)
--                 → drop-irrel i (suc n) i≤sn (x ∷ xs) ≡ drop-irrel i n i≤n xs
-- drop-irrel-lem₁ i n i≤sn i≤n x xs with ℕ.compare i (suc n)
-- drop-irrel-lem₁ i .(i ℕ.+ k) i≤sn i≤n x xs | ℕ.less .i k = ≡.refl
-- drop-irrel-lem₁ .(suc n) n i≤sn i≤n x xs | ℕ.equal .(suc n) = Irrelevant.⊥-elim (contra₂ _ i≤n)
-- drop-irrel-lem₁ .(suc (suc (n ℕ.+ k))) n i≤sn i≤n x xs | ℕ.greater .(suc n) k = Irrelevant.⊥-elim (contra₁ _ _ (≤-pred-both i≤sn))

-- drop-irrel-lem₂ : ∀ i
--                 → .(i≤n : i ≤ i)
--                 → (xs : Vec Carrier i)
--                 → drop-irrel i i i≤n xs ≡ xs
-- drop-irrel-lem₂ i i≤n xs with ℕ.compare i i
-- drop-irrel-lem₂ i i≤n xs | res = {!res!}

-- drop-irrel-correct : ∀ {i n}
--                    → (i≤n : i ≤ n)
--                    → (xs : Vec Carrier n)
--                    → drop i≤n xs ≡ drop-irrel i n i≤n xs
-- drop-irrel-correct {i} {.i} m≤m xs = {!!}
-- drop-irrel-correct {i} {.(suc _)} (≤-s i≤n) (x ∷ xs) = ≡.trans (drop-irrel-correct i≤n xs) (≡.sym (drop-irrel-lem₁ _ _ (≤-s i≤n) i≤n x xs))
