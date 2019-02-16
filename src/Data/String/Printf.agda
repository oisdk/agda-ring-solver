module Data.String.Printf where

open import Data.List using (List; []; _∷_; foldr)
open import Data.String hiding (show)
open import Data.Nat hiding (_≟_)
open import Data.Char using (Char)
open import Data.Char.Unsafe using (_≟_)
import Level
open import Relation.Nullary

infixr 6 _%_
record FormatUnit : Set (Level.suc Level.zero) where
  constructor _%_
  field
    marker : Char
    {type} : Set
    conv   : type → String
open FormatUnit public

module Internal where
  data Formatter : Set (Level.suc Level.zero) where
    chr : Char → Formatter
    cnv : (t : Set) → (t → String) → Formatter

  formatUnitTy : Formatter → Set → Set
  formatUnitTy (chr _) xs = xs
  formatUnitTy (cnv t _) xs = t → xs

  formatTy : List Formatter → Set
  formatTy = foldr formatUnitTy String

  toFormat : List FormatUnit → List Char → List Formatter
  toFormat fs [] = []
  toFormat fs ('%' ∷ x ∷ xs) = go fs x xs where
    go : List FormatUnit → Char → List Char → List Formatter
    go [] x xs = chr x ∷ toFormat fs xs
    go (f ∷ fs) x xs with marker f ≟ x
    go (f ∷ _ ) x xs | yes p = cnv _ (conv f) ∷ toFormat fs xs
    go (f ∷ fs) x xs | no ¬p = go fs x xs
  toFormat fs (x ∷ xs) = chr x ∷ toFormat fs xs

  printf : (fs : List FormatUnit) → (xs : String) → formatTy (toFormat fs (toList xs))
  printf fs xs = go "" (toFormat fs (toList xs))
    where
    go : String → (xs : List Formatter) → formatTy xs
    go k [] = k
    go k (chr x ∷ xs) = go (k ++ fromList (x ∷ [])) xs
    go k (cnv _ c ∷ xs) = λ x → go (k ++ c x) xs
import Data.Nat.Show
open import Function

standard : List FormatUnit
standard = 'i' % Data.Nat.Show.show ∷ 's'% id ∷ []

module Printf (fs : List FormatUnit) where
  printf : (xs : String) → Internal.formatTy (Internal.toFormat fs (toList xs))
  printf = Internal.printf fs
