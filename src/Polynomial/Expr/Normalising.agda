{-# OPTIONS --without-K --safe #-}

open import Algebra
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.String using (String)
open import EqBool
open import Data.Bool

module Polynomial.Expr.Normalising
  {r}
  (ring : RawRing r)
  (show : RawRing.Carrier ring → String)
  ⦃ _ : HasEqBool (RawRing.Carrier ring) ⦄
  where

open RawRing ring

-- An expressions which contains some free variables.
infixl 6 _⊕_
infixl 7 _⊗_
data Open : Set r where
  V : String → Open
  K : Carrier → Open
  _⊕_ : Open → Open → Open
  _⊗_ : Open → Open → Open
  ⊝_ : Open → Open

_==O_ : Open → Open → Bool
_==O_ (V v) (V y) = v == y
_==O_ (K k) (K y) = k == y
_==O_ (x₁ ⊕ y₁) (x₂ ⊕ y₂) = x₁ ==O x₂ ∧ y₁ ==O y₂
_==O_ (x₁ ⊗ y₁) (x₂ ⊗ y₂) = x₁ ==O x₂ ∧ y₁ ==O y₂
_==O_ (⊝ x) (⊝ y) = x ==O y
_==O_ _ _ = false

instance
  eqOpen : HasEqBool Open
  _==_ ⦃ eqOpen ⦄ = _==O_

-- An expression which might not have any free variables
data Expr : Set r where
  C : Carrier → Expr
  O : Open → Expr

instance
  eqExpr : HasEqBool Expr
  _==_ ⦃ eqExpr ⦄ (C x₁) (C x₂) = x₁ == x₂
  _==_ ⦃ eqExpr ⦄ (C x₁) (O x₂) = false
  _==_ ⦃ eqExpr ⦄ (O x₁) (C x₂) = false
  _==_ ⦃ eqExpr ⦄ (O x₁) (O x₂) = x₁ == x₂

normalise : Expr → Expr
normalise (C x) = C x
normalise (O x) = go x
  where
  go : Open → Expr
  go (V v) = O (V v)
  go (K k) = C k
  go (x ⊕ y) with go x | go y
  go (x ⊕ y) | C x₁ | C x₂ = C (x₁ + x₂)
  go (x ⊕ y) | C x₁ | O x₂ = if x₁ == 0# then O x₂ else O (K x₁ ⊕ x₂)
  go (x ⊕ y) | O x₁ | C x₂ = if x₂ == 0# then O x₁ else O (x₁ ⊕ K x₂)
  go (x ⊕ y) | O x₁ | O x₂ = O (x₁ ⊕ x₂)
  go (x ⊗ y) with go x | go y
  go (x ⊗ y) | C x₁ | C x₂ = C (x₁ + x₂)
  go (x ⊗ y) | C x₁ | O x₂ = if x₁ == 0# then C 0# else if x₁ == 1# then O x₂ else O (K x₁ ⊗ x₂)
  go (x ⊗ y) | O x₁ | C x₂ = if x₂ == 0# then C 0# else if x₂ == 1# then O x₁ else O (x₁ ⊗ K x₂)
  go (x ⊗ y) | O x₁ | O x₂ = O (x₁ ⊗ x₂)
  go (⊝ x) with go x
  go (⊝ x) | C x₁ = C (- x₁)
  go (⊝ x) | O x₁ = O (⊝ x₁)

open import Data.List.Kleene
open import Data.Product
open import Data.Nat

data Flat : Set r where
  sum : Flat ⁺ → Flat
  prd : (Flat × ℕ) ⁺ → Flat
  neg : Flat → Flat
  V′ : String → Flat
  K′ : Carrier → Flat

mutual
  _==F⋆_ : Flat ⋆ → Flat ⋆ → Bool
  [] ==F⋆ [] = true
  [] ==F⋆ [ x₁ ] = false
  [ x₁ ] ==F⋆ [] = false
  [ x & xs ] ==F⋆ [ y & ys ] = x ==F y ∧ xs ==F⋆ ys

  _==F×⋆_ : (Flat × ℕ) ⋆ → (Flat × ℕ) ⋆ → Bool
  [] ==F×⋆ [] = true
  [] ==F×⋆ [ x₁ ] = false
  [ x₁ ] ==F×⋆ [] = false
  [ (x , i) & xs ] ==F×⋆ [ (y , j) & ys ] = i == j ∧ x ==F y ∧ xs ==F×⋆ ys

  _==F_ : Flat → Flat → Bool
  _==F_ (sum (x & xs)) (sum (y & ys)) = x ==F y ∧ xs ==F⋆ ys
  _==F_ (prd ((x , i) & xs)) (prd ((y , j) & ys)) = i == j ∧ x ==F y ∧ xs ==F×⋆ ys
  _==F_ (neg xs) (neg ys) = xs ==F ys
  _==F_ (V′ x)   (V′ y)   = x == y
  _==F_ (K′ x)   (K′ y)   = x == y
  _==F_ _ _ = false

instance
  eqFlat : HasEqBool Flat
  _==_ ⦃ eqFlat ⦄ = _==F_

prodCons : Flat → (Flat × ℕ) ⋆ → (Flat × ℕ) ⁺
prodCons x [] = (x , 0) & []
prodCons x [ (y , n) & xs ] with x == y
prodCons x xs@([ (y , n) & ys ]) | false = (x , 0) & xs
prodCons x [ (y , n) & xs ] | true = (y , suc n) & xs

flatten : Open → Flat
flatten (V x) = V′ x
flatten (K x) = K′ x
flatten (x ⊕ y) = sum (x ⊕⋆ [ y ⊕⋆ [] ])
  where
  _⊕⋆_ : Open → Flat ⋆ → Flat ⁺
  (x ⊕ y) ⊕⋆ xs = x ⊕⋆ [ y ⊕⋆ xs ]
  x ⊕⋆ xs = flatten x & xs
flatten (x ⊗ y) = prd (x ⊗⋆ [ y ⊗⋆ [] ])
  where
  _⊗⋆_ : Open → (Flat × ℕ) ⋆ → (Flat × ℕ) ⁺
  (x ⊗ y) ⊗⋆ xs = x ⊗⋆ [ y ⊗⋆ xs ]
  x ⊗⋆ xs = prodCons (flatten x) xs
flatten (⊝ x) = neg (flatten x)

⟨_⟩ₑ : Expr → String
⟨ C x ⟩ₑ = show x
⟨ O x ⟩ₑ = Data.String.fromList (go add (flatten x) List.[])
  where
  import Data.String
  open import Data.Char using (Char)
  open import Data.List.Kleene
  open import Data.List as List using (List; _∷_)
  import Data.Nat.Show

  data PrecLevel : Set where
    mul add neg′ : PrecLevel

  go : PrecLevel → Flat → List Char → List Char

  gop : (Flat × ℕ) → List Char → List Char
  gop (x , zero) = go mul x
  gop (x , suc i) xs = go neg′ x (' ' ∷ '^' ∷ ' ' ∷ Data.String.toList (Data.Nat.Show.show (suc (suc i))) List.++ (' ' ∷ xs))

  f-+ : List Char → Flat ⋆ → List Char
  f-+ xs [ x & zs ] = ' ' ∷ '+' ∷ ' ' ∷ go add x (f-+ xs zs)
  f-+ xs [] = xs

  f-× : List Char → (Flat × ℕ) ⋆ → List Char
  f-× xs [ x & zs ] = ' ' ∷ '*' ∷ ' ' ∷ gop x (f-× xs zs)
  f-× xs [] = xs

  go _ (V′ x) xs = Data.String.toList x List.++ xs
  go _ (K′ x) xs = Data.String.toList (show x) List.++ xs
  go neg′ (neg x) xs = '(' ∷ '-' ∷ ' ' ∷ go neg′ x (')' ∷ xs)
  go _   (neg x) xs = '-' ∷ ' ' ∷ go neg′ x xs
  go add (sum (z & zs)) xs = go add z (f-+ xs zs)
  go _   (sum (z & zs)) xs = '(' ∷ go add z (f-+ (')' ∷ xs) zs)
  go neg′ (prd (z & zs)) xs = '(' ∷ gop z (f-× (')' ∷ xs) zs)
  go _    (prd (z & zs)) xs = gop z (f-× xs zs)
