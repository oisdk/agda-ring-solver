module Polynomials.Simple.Reflection where

open import Reflection
open import Data.Maybe
open import Polynomials.Expr
open import Polynomials.Simple.AlmostCommutativeRing
open import Relation.Nullary
open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Fin as Fin
open import Data.List hiding (fromMaybe)
open import Data.Unit
open import Data.Maybe
open import Function
import Level
open import Data.Product
open import Function

module Internal where

  -- Some patterns to decrease verbosity
  infixr 5 ⟨_⟩∷_ ⟅_⟆∷_
  pattern ⟨_⟩∷_ x xs = arg (arg-info visible relevant) x ∷ xs
  pattern ⟅_⟆∷_ x xs = arg (arg-info hidden relevant) x ∷ xs

  natTerm : ℕ → Term
  natTerm zero = quote zero ⟨ con ⟩ []
  natTerm (suc i) = quote suc ⟨ con ⟩ ⟨ natTerm i ⟩∷ []

  -- This function applies the hidden arguments that the constructors
  -- for Expr need. The first is the universe level, the second is the
  -- type it contains, and the third is the number of variables it's
  -- indexed by. All three of these could likely be inferred, but to
  -- make things easier we supply the third because we know it.
  infixr 5 ⟅_⋯⟆∷_
  ⟅_⋯⟆∷_ : ℕ → List (Arg Term) → List (Arg Term)
  ⟅ i ⋯⟆∷ xs = ⟅ unknown ⟆∷ ⟅ unknown ⟆∷ ⟅ natTerm i ⟆∷ xs

  -- A constant expression.
  constExpr : ℕ → Term → Term
  constExpr i x = quote Κ ⟨ con ⟩ ⟅ i ⋯⟆∷ ⟨ x ⟩∷ []

  mutual
    -- Application of a ring operator often doesn't have a type as
    -- simple as "Carrier → Carrier → Carrier": there may be hidden
    -- arguments, etc. Here, we do our best to handle those cases,
    -- by just taking the last two explicit arguments.
    getBinOp : ℕ → Name → List (Arg Term) → Term
    getBinOp i nm (⟨ x ⟩∷ ⟨ y ⟩∷ []) = nm ⟨ con ⟩ ⟅ i ⋯⟆∷ ⟨ toExpr i x ⟩∷ ⟨ toExpr i y ⟩∷ []
    getBinOp i nm (x ∷ xs) = getBinOp i nm xs
    getBinOp _ _ _ = unknown

    getUnOp : ℕ → Name → List (Arg Term) → Term
    getUnOp i nm (⟨ x ⟩∷ []) = nm ⟨ con ⟩ ⟅ i ⋯⟆∷ ⟨ toExpr i x ⟩∷ []
    getUnOp i nm (x ∷ xs) = getUnOp i nm xs
    getUnOp _ _ _ = unknown

    -- When trying to figure out the shape of an expression, one of
    -- the difficult tasks is recognizing where constants in the
    -- underlying ring are used. If we were only dealing with ℕ, we
    -- might look for its constructors: however, we want to deal with
    -- arbitrary types which implement AlmostCommutativeRing. If the
    -- Term type contained type information we might be able to
    -- recognize it there, but it doesn't.
    --
    -- We're in luck, though, because all other cases in the following
    -- function *are* recognizable. As a result, the "catch-all" case
    -- will just assume that it has a constant expression.
    toExpr : (i : ℕ) → Term → Term
    toExpr i t@(def f xs) with f ≟-Name quote AlmostCommutativeRing._+_
    ... | yes p = getBinOp i (quote _⊕_) xs
    ... | no _ with f ≟-Name quote AlmostCommutativeRing._*_
    ... | yes p = getBinOp i (quote _⊗_) xs
    ... | no _ with f ≟-Name quote AlmostCommutativeRing.-_
    ... | yes p = getUnOp i (quote ⊝_) xs
    ... | no _ = constExpr i t
    toExpr i v@(var x args) with suc x ℕ.≤? i
    ... | yes p = v
    ... | no ¬p = constExpr i v
    {-# CATCHALL #-}
    toExpr i t = constExpr i t

  open import Polynomials.Simple.Solver renaming (solve to solve′)

  open import Data.String

  hlams : List String → Term → Term
  hlams vs xs = foldr (λ v vs → lam hidden (abs v vs)) xs vs

  vlams : List String → Term → Term
  vlams vs xs = foldr (λ v vs → lam visible (abs v vs)) xs vs

  mkSolver : List String → Name → ℕ → Term → Term → Term
  mkSolver nms rng i lhs rhs =
    quote solve′ ⟨ def ⟩
      ⟅ unknown ⟆∷
      ⟅ unknown ⟆∷
      ⟨ def rng [] ⟩∷
      ⟨ natTerm i ⟩∷
      ⟨ vlams nms $
          quote _⊜_ ⟨ def ⟩
            ⟅ unknown ⟆∷
            ⟅ unknown ⟆∷
            ⟨ def rng [] ⟩∷
            ⟨ natTerm i ⟩∷
            ⟨ toExpr i lhs ⟩∷
            ⟨ toExpr i rhs ⟩∷
            []
      ⟩∷
      ⟨ hlams nms $
          quote AlmostCommutativeRing.refl ⟨ def ⟩
            ⟅ unknown ⟆∷
            ⟅ unknown ⟆∷
            ⟨ def rng [] ⟩∷
            ⟅ unknown ⟆∷
            []
      ⟩∷
      []


  toSoln : Name → Term → Term
  toSoln rng = go 0 id
    where
    go : ℕ → (List String → List String) → Term → Term
    go i k (def f (⟨ lhs ⟩∷ ⟨ rhs ⟩∷ [])) = mkSolver (k []) rng i lhs rhs
    go i k (def f (_ ∷ _ ∷ ⟨ lhs ⟩∷ ⟨ rhs ⟩∷ [])) = mkSolver (k []) rng i lhs rhs
    go i k (def f (_ ∷ _ ∷ _ ∷ ⟨ lhs ⟩∷ ⟨ rhs ⟩∷ [])) = mkSolver (k []) rng i lhs rhs
    go i k (pi a (abs s x)) = go (suc i) (k ∘ (s ∷_)) x
    go i k t = unknown

open Internal
open import Agda.Builtin.Reflection
macro
  solve : Name → Term → TC ⊤
  solve rng hole =
    inferType hole ⟨ bindTC ⟩ reduce ⟨ bindTC ⟩ unify hole ∘ toSoln rng
