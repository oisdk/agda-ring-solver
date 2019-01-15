module FastFoldr where

open import Data.List using (List; _∷_; [])

foldr : ∀ {a b} {A : Set a} {B : Set b}
      → (A → B → B)
      → B
      → List A
      → B
foldr f b [] = b
foldr f b (x ∷ xs) = f x (foldr f b xs)

{-# COMPILE GHC foldr = \_ _ _ _ -> foldr #-}
