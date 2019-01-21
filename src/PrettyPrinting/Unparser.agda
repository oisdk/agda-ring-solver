module PrettyPrinting.Unparser where

open import Data.Char
open import Data.List
open import Data.Nat using (ℕ; suc; zero)
open import Data.String using (String; fromList; toList)
open import Function
open import Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (_==_; _<_)
open import Data.Bool

data Side : Set where
  left : Side
  right : Side

diffSide : Side → Side → Bool
diffSide left left = false
diffSide left right = true
diffSide right left = true
diffSide right right = false

record Op : Set where
  constructor op
  field
    prec : ℕ
    assoc : Side
open Op

data ShowExpr : Set where
  lit : String → ShowExpr
  pre : String → Op → ShowExpr → ShowExpr
  bin : String → Op → ShowExpr → ShowExpr → ShowExpr

showExpr : ShowExpr → String
showExpr expr = fromList (go expr [])
  where
  if-prns : Side → Op → Maybe Op → (List Char → List Char) → List Char → List Char
  if-prns sid o (just i) n a = if (prec i < prec o) ∨ ((prec i == prec o) ∧ (diffSide (assoc o) (assoc i) ∨ diffSide sid (assoc o))) then '(' ∷ n (')' ∷ a) else n a
  if-prns sid x nothing = id

  getOp : ShowExpr → Maybe Op
  getOp (lit x) = nothing
  getOp (bin x x₁ x₂ x₃) = just x₁
  getOp (pre _ x _) = just x

  go : ShowExpr → List Char → List Char
  go (lit x) a = toList x ++ a
  go (pre t o y) = (toList t ++_) ∘ if-prns right o (getOp y) (go y)
  go (bin t o x y) = if-prns left o (getOp x) (go x) ∘ (toList t ++_) ∘ if-prns right o (getOp y) (go y)
