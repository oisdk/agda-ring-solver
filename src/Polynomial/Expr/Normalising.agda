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

instance
  eqOpen : HasEqBool Open
  _==_ ⦃ eqOpen ⦄ (V v) (V y) = v == y
  _==_ ⦃ eqOpen ⦄ (K k) (K y) = k == y
  _==_ ⦃ eqOpen ⦄ (x₁ ⊕ y₁) (x₂ ⊕ y₂) = x₁ == x₂ ∧ y₁ == y₂
  _==_ ⦃ eqOpen ⦄ (x₁ ⊗ y₁) (x₂ ⊗ y₂) = x₁ == x₂ ∧ y₁ == y₂
  _==_ ⦃ eqOpen ⦄ (⊝ x) (⊝ y) = x == y
  _==_ ⦃ eqOpen ⦄ _ _ = false

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

data Flat : Set r where
  sum : Flat ⁺ → Flat
  prd : Flat ⁺ → Flat
  neg : Flat → Flat
  V′ : String → Flat
  K′ : Carrier → Flat

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
  _⊗⋆_ : Open → Flat ⋆ → Flat ⁺
  (x ⊗ y) ⊗⋆ xs = x ⊗⋆ [ y ⊗⋆ xs ]
  x ⊗⋆ xs = flatten x & xs
flatten (⊝ x) = neg (flatten x)

prettyExpr : Expr → String
prettyExpr (C x) = show x
prettyExpr (O x) = Data.String.fromList (go add (flatten x) List.[])
  where
  import Data.String
  open import Data.Char using (Char)
  open import Data.List.Kleene
  open import Data.List as List using (List; _∷_)

  data PrecLevel : Set where
    mul add neg′ : PrecLevel

  go : PrecLevel → Flat → List Char → List Char

  f : PrecLevel → Char → List Char → Flat ⋆ → List Char
  f p o xs [ x & zs ] = ' ' ∷ o ∷ ' ' ∷ go p x (f p o xs zs)
  f p o xs [] = xs

  go _ (V′ x) xs = Data.String.toList x List.++ xs
  go _ (K′ x) xs = Data.String.toList (show x) List.++ xs
  go neg′ (neg x) xs = '(' ∷ '-' ∷ ' ' ∷ go neg′ x (')' ∷ xs)
  go _   (neg x) xs = '-' ∷ ' ' ∷ go neg′ x xs
  go add (sum (z & zs)) xs = go add z (f add '+' xs zs)
  go _   (sum (z & zs)) xs = '(' ∷ go add z (f add '+' (')' ∷ xs) zs)
  go neg′ (prd (z & zs)) xs = '(' ∷ go mul z (f mul '*' (')' ∷ xs) zs)
  go _    (prd (z & zs)) xs = go mul z (f mul '*' xs zs)
