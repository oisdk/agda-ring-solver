module Polynomial.Simple.Reflection where

open import Reflection
open import Function
open import Data.Unit using (⊤)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using (List; _∷_; []; foldr)

module Internal (rng : Term) where
  open import Polynomial.Simple.Solver renaming (solve to solve′)
  open import Data.String
  open import Relation.Nullary using (Dec; yes; no)
  import Data.Vec as Vec
  import Data.Fin as Fin

  -- Some patterns to decrease verbosity
  infixr 5 _⟨∷⟩_ _⟅∷⟆_
  pattern _⟨∷⟩_ x xs = arg (arg-info visible relevant) x ∷ xs
  pattern _⟅∷⟆_ x xs = arg (arg-info hidden relevant) x ∷ xs

  infixr 5 _⋯⟅∷⟆_
  _⋯⟅∷⟆_ : ℕ → List (Arg Term) → List (Arg Term)
  zero ⋯⟅∷⟆ xs = xs
  suc i ⋯⟅∷⟆ xs = unknown ⟅∷⟆  i ⋯⟅∷⟆ xs

  natTerm : ℕ → Term
  natTerm zero = quote zero ⟨ con ⟩ []
  natTerm (suc i) = quote suc ⟨ con ⟩ natTerm i ⟨∷⟩ []

  finTerm : ℕ → Term
  finTerm zero = quote Fin.zero ⟨ con ⟩ 1 ⋯⟅∷⟆ []
  finTerm (suc i) = quote Fin.suc ⟨ con ⟩ 1 ⋯⟅∷⟆ finTerm i ⟨∷⟩ []

  curriedTerm : ℕ → Term
  curriedTerm = go zero
    where
    go : ℕ → ℕ → Term
    go k zero = quote Vec.[] ⟨ con ⟩ 2 ⋯⟅∷⟆ []
    go k (suc i) = quote Vec._∷_ ⟨ con ⟩ 2 ⋯⟅∷⟆ 1 ⋯⟅∷⟆ var k [] ⟨∷⟩ go (suc k) i ⟨∷⟩ []

  hlams : List String → Term → Term
  hlams vs xs = foldr (λ v vs → lam hidden (abs v vs)) xs vs

  vlams : List String → Term → Term
  vlams vs xs = foldr (λ v vs → lam visible (abs v vs)) xs vs

  module _ (numVars : ℕ) where

    -- This function applies the hidden arguments that the constructors
    -- that Expr needs. The first is the universe level, the second is the
    -- type it contains, and the third is the number of variables it's
    -- indexed by. All three of these could likely be inferred, but to
    -- make things easier we supply the third because we know it.
    infixr 5 E⟅∷⟆_
    E⟅∷⟆_ : List (Arg Term) → List (Arg Term)
    E⟅∷⟆ xs = 1 ⋯⟅∷⟆
              (quote AlmostCommutativeRing.Carrier ⟨ def ⟩ 2 ⋯⟅∷⟆ rng ⟨∷⟩ []) ⟅∷⟆
              natTerm numVars ⟅∷⟆
              xs

    -- A constant expression.
    constExpr : Term → Term
    constExpr x = quote Κ ⟨ con ⟩ E⟅∷⟆ x ⟨∷⟩ []

    module ToExpr (varExpr : ℕ → Term) where
      mutual
        -- Application of a ring operator often doesn't have a type as
        -- simple as "Carrier → Carrier → Carrier": there may be hidden
        -- arguments, etc. Here, we do our best to handle those cases,
        -- by just taking the last two explicit arguments.
        getBinOp : Name → List (Arg Term) → Term
        getBinOp nm (x ⟨∷⟩ y ⟨∷⟩ []) = nm ⟨ con ⟩ E⟅∷⟆ toExpr x ⟨∷⟩ toExpr y ⟨∷⟩ []
        getBinOp nm (x ∷ xs) = getBinOp nm xs
        getBinOp _ _ = unknown

        getUnOp : Name → List (Arg Term) → Term
        getUnOp nm (x ⟨∷⟩ []) = nm ⟨ con ⟩ E⟅∷⟆ toExpr x ⟨∷⟩ []
        getUnOp nm (x ∷ xs) = getUnOp nm xs
        getUnOp _ _ = unknown

        getExp : List (Arg Term) → Term
        getExp (x ⟨∷⟩ y ⟨∷⟩ []) = quote _⊛_ ⟨ con ⟩ E⟅∷⟆ toExpr x ⟨∷⟩ y ⟨∷⟩ []
        getExp (x ∷ xs) = getExp xs
        getExp _ = unknown

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
        toExpr : Term → Term
        toExpr (def (quote AlmostCommutativeRing._+_) xs) = getBinOp (quote _⊕_) xs
        toExpr (def (quote AlmostCommutativeRing._*_) xs) = getBinOp (quote _⊗_) xs
        toExpr (def (quote AlmostCommutativeRing._^_) xs) = getExp xs
        toExpr (def (quote AlmostCommutativeRing.-_) xs) = getUnOp (quote ⊝_) xs
        toExpr v@(var x args) with x ℕ.<? numVars
        ... | yes p = varExpr x
        ... | no ¬p = constExpr v
        {-# CATCHALL #-}
        toExpr t = constExpr t

    mkSolver : List String → Term → Term → List (Arg Type)
    mkSolver nms lhs rhs =
        2 ⋯⟅∷⟆
        rng ⟨∷⟩
        natTerm numVars ⟨∷⟩
        vlams nms (quote _⊜_ ⟨ def ⟩ 2 ⋯⟅∷⟆ rng ⟨∷⟩ natTerm numVars ⟨∷⟩ toExpr lhs ⟨∷⟩ toExpr rhs ⟨∷⟩ []) ⟨∷⟩
        hlams nms (quote AlmostCommutativeRing.refl ⟨ def ⟩ 2 ⋯⟅∷⟆ rng ⟨∷⟩ 1 ⋯⟅∷⟆ []) ⟨∷⟩
        []
      where
      open ToExpr (λ x → var x [])

    mkSolver′ : Term → Term → Term
    mkSolver′ lhs rhs =
      quote AlmostCommutativeRing.trans ⟨ def ⟩
        2 ⋯⟅∷⟆
        rng ⟨∷⟩
        3 ⋯⟅∷⟆
        (quote AlmostCommutativeRing.sym ⟨ def ⟩
            (2 ⋯⟅∷⟆
            rng ⟨∷⟩
            2 ⋯⟅∷⟆
            (quote Ops.correct ⟨ def ⟩ 2 ⋯⟅∷⟆ rng ⟨∷⟩ 1 ⋯⟅∷⟆ toExpr lhs ⟨∷⟩ ρ ⟨∷⟩ []) ⟨∷⟩
            []))
        ⟨∷⟩
        (quote Ops.correct ⟨ def ⟩ 2 ⋯⟅∷⟆ rng ⟨∷⟩ 1 ⋯⟅∷⟆ toExpr rhs ⟨∷⟩ ρ ⟨∷⟩ []) ⟨∷⟩
        []
      where
      open ToExpr (λ x → quote Ι ⟨ con ⟩ E⟅∷⟆ finTerm x ⟨∷⟩ [])
      ρ : Term
      ρ = curriedTerm numVars

  toSoln : Term → Term
  toSoln = go 0 id
    where
    go : ℕ → (List String → List String) → Term → Term
    go i k (def f (            lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = quote solve′ ⟨ def ⟩ mkSolver i (k []) lhs rhs
    go i k (def f (    _ ∷ _ ∷ lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = quote solve′ ⟨ def ⟩ mkSolver i (k []) lhs rhs
    go i k (def f (_ ∷ _ ∷ _ ∷ lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = quote solve′ ⟨ def ⟩ mkSolver i (k []) lhs rhs
    go i k (pi a (abs s x)) = go (suc i) (k ∘ (s ∷_)) x
    go i k t = unknown

  toSoln′ : ℕ → Term → Term
  toSoln′ i (def f (            lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = mkSolver′ i lhs rhs
  toSoln′ i (def f (_ ∷ _ ∷     lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = mkSolver′ i lhs rhs
  toSoln′ i (def f (_ ∷ _ ∷ _ ∷ lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = mkSolver′ i lhs rhs
  toSoln′ _ _ = unknown

open Internal
open import Agda.Builtin.Reflection

-- This is the main macro you'll probably be using. Call it like this:
--
--   lemma : ∀ x y → x + y ≈ y + x
--   lemma = solver TypeRing
--
-- where TypRing is your implementation of AlmostCommutativeRing. (Find some
-- example implementations in Polynomial.Solver.Ring.AlmostCommutativeRing.Instances).
macro
  solve : Name → Term → TC ⊤
  solve rng hole =
    inferType hole ⟨ bindTC ⟩ reduce ⟨ bindTC ⟩ unify hole ∘ toSoln (def rng [])

-- Use this macro when you want to solve something *under* a lambda. For example:
-- say you have a long proof, and you just want the solver to deal with an
-- intermediate step. Call it like so:
--
--   lemma₃ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
--   lemma₃ x y = begin
--     x + y * 1 + 3 ≈⟨ +-comm x (y * 1) ⟨ +-cong ⟩ refl ⟩
--     y * 1 + x + 3 ≋⟨ solveFor 2 Int.ring ⟩
--     3 + y + x     ≡⟨ refl ⟩
--     2 + 1 + y + x ∎
--
-- The first argument is the number of free variables, and the second is the
-- ring implementation (as before).
--
-- One thing to note here is that we need to be able to infer *both* sides of
-- the equality, which the normal equaltional reasoning combinators don't let you
-- do. You'll need a special combinator, defined in Relation.Binary.Reasoning.Inference.
macro
  solveFor : ℕ → Name → Term → TC ⊤
  solveFor i rng hole =
    inferType hole ⟨ bindTC ⟩ reduce ⟨ bindTC ⟩ unify hole ∘ toSoln′ (def rng []) i
