{-# OPTIONS --without-K --safe #-}

module Reflection.Helpers where

open import Agda.Builtin.Reflection
open import Reflection
open import Function
open import Data.List as List using (List; _∷_; [])
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Nat.GeneralisedArithmetic using (fold)
open import Data.Fin as Fin using (Fin)
open import Data.Vec as Vec using (Vec)
open import Data.Nat.Table as Table using (Table)
open import Data.String using (String)
open import Data.Maybe as Maybe using (Maybe; just; nothing)

module _ {a} {A : Set a} where
  pure : A → TC A
  pure = returnTC

  infixl 3 _<|>_
  _<|>_ : TC A → TC A → TC A
  _<|>_ = catchTC

module _ {a b} {A : Set a} {B : Set b} where
  infixl 1 _>>=_ _>>_
  _>>=_ : TC A → (A → TC B) → TC B
  _>>=_ = bindTC

  _>>_ : TC A → TC B → TC B
  xs >> ys = xs ⟨ bindTC ⟩ λ _ → ys

  infixl 4 _<$>_ _<*>_ _<$_
  _<*>_ : TC (A → B) → TC A → TC B
  fs <*> xs = fs ⟨ bindTC ⟩ λ f → xs ⟨ bindTC ⟩ λ x → returnTC (f x)

  _<$>_ : (A → B) → TC A → TC B
  f <$> xs = xs ⟨ bindTC ⟩ λ x → pure (f x)

  _<$_ : A → TC B → TC A
  x <$ xs = xs ⟨ bindTC ⟩ λ _ → pure x

infixr 5 _⟨∷⟩_ _⟅∷⟆_
pattern _⟨∷⟩_ x xs = arg (arg-info visible relevant) x ∷ xs
pattern _⟅∷⟆_ x xs = arg (arg-info hidden  relevant) x ∷ xs

infixr 5 _⋯⟅∷⟆_
_⋯⟅∷⟆_ : ℕ → List (Arg Term) → List (Arg Term)
zero  ⋯⟅∷⟆ xs = xs
suc i ⋯⟅∷⟆ xs = unknown ⟅∷⟆ i ⋯⟅∷⟆ xs

natTerm : ℕ → Term
natTerm zero = quote zero ⟨ con ⟩ []
natTerm (suc i) = quote suc ⟨ con ⟩ natTerm i ⟨∷⟩ []

finTerm : ℕ → Term
finTerm zero = quote Fin.zero ⟨ con ⟩ 1 ⋯⟅∷⟆ []
finTerm (suc i) = quote Fin.suc ⟨ con ⟩ 1 ⋯⟅∷⟆ finTerm i ⟨∷⟩ []

curriedTerm : Table → Term
curriedTerm = List.foldr go (quote Vec.[] ⟨ con ⟩ 2 ⋯⟅∷⟆ []) ∘ Table.toList
  where
  go : ℕ → Term → Term
  go x xs = quote Vec._∷_ ⟨ con ⟩ 3 ⋯⟅∷⟆ var x [] ⟨∷⟩ xs ⟨∷⟩ []

hlams : List String → Term → Term
hlams vs xs = List.foldr (λ v vs → lam hidden (abs v vs)) xs vs

vlams : List String → Term → Term
vlams vs xs = List.foldr (λ v vs → lam visible (abs v vs)) xs vs


example : TC Term → TC (List (Arg Term)) → TC (List (Arg Term))
example x xs = ⦇ x ⟨∷⟩ xs ⦈
