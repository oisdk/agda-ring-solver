{-# OPTIONS --without-K --safe #-}

module Polynomial.Simple.Reflection where

open import Agda.Builtin.Reflection
open import Reflection
open import Function
open import Data.Unit using (⊤; tt)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using (List; _∷_; []; foldr)
open import Reflection.Helpers
open import Data.Bool as Bool using (Bool; if_then_else_; true; false)

module Internal (rng : Term) where
  open import Polynomial.Simple.Solver renaming (solve to solve′)
  open import Data.String
  open import Relation.Nullary using (Dec; yes; no)
  import Data.Vec as Vec
  import Data.Fin as Fin
  open import Data.Maybe as Maybe using (Maybe; just; nothing)
  open AlmostCommutativeRing

  open import Data.Nat.Table

  getName : Name → TC (Maybe Name)
  getName nm = go <$> normalise (nm ⟨ def ⟩ 2 ⋯⟅∷⟆ rng ⟨∷⟩ [])
    where
    go : Term → Maybe Name
    go (def f args) = just f
    go _ = nothing

  module _ (numVars : ℕ) where

    -- This function applies the hidden arguments that the constructors
    -- that Expr needs. The first is the universe level, the second is the
    -- type it contains, and the third is the number of variables it's
    -- indexed by. All three of these could likely be inferred, but to
    -- make things easier we supply the third because we know it.
    infixr 5 E⟅∷⟆_
    E⟅∷⟆_ : List (Arg Term) → List (Arg Term)
    E⟅∷⟆ xs = 1 ⋯⟅∷⟆
              (quote Carrier ⟨ def ⟩ 2 ⋯⟅∷⟆ rng ⟨∷⟩ []) ⟅∷⟆
              natTerm numVars ⟅∷⟆
              xs

    -- A constant expression.
    constExpr : Term → Term
    constExpr x = quote Κ ⟨ con ⟩ E⟅∷⟆ x ⟨∷⟩ []

    matchName : Maybe Name → Name → Bool
    matchName nothing _ = false
    matchName (just x) y with x ≟-Name y
    ... | yes p = true
    ... | no ¬p = false

    module ToExpr (varExpr : ℕ → Maybe Term) (+-nm : Maybe Name) (*-nm : Maybe Name) (^-nm : Maybe Name) (-‿nm : Maybe Name)  where
      mutual
        -- Application of a ring operator often doesn't have a type as
        -- simple as "Carrier → Carrier → Carrier": there may be hidden
        -- arguments, etc. Here, we do our best to handle those cases,
        -- by just taking the last two explicit arguments.
        getBinOp : Name → List (Arg Term) → TC Term
        getBinOp nm (x ⟨∷⟩ y ⟨∷⟩ []) = con nm ∘′ E⟅∷⟆_ <$> ⦇ toExpr x ⟨∷⟩ ⦇ toExpr y ⟨∷⟩ pure [] ⦈ ⦈
        getBinOp nm (x ∷ xs) = getBinOp nm xs
        getBinOp _ _ = typeError (strErr "getBinOp" ∷ [])

        getUnOp : Name → List (Arg Term) → TC Term
        getUnOp nm (x ⟨∷⟩ []) = (λ x′ → nm ⟨ con ⟩ E⟅∷⟆ x′ ⟨∷⟩ []) <$> toExpr x
        getUnOp nm (x ∷ xs) = getUnOp nm xs
        getUnOp _ _ = typeError (strErr "getUnOp" ∷ [])

        getExp : List (Arg Term) → TC Term
        getExp (x ⟨∷⟩ y ⟨∷⟩ []) = (λ x′ → quote _⊛_ ⟨ con ⟩ E⟅∷⟆ x′ ⟨∷⟩ y ⟨∷⟩ []) <$> toExpr x
        getExp (x ∷ xs) = getExp xs
        getExp _ = typeError (strErr "getExp" ∷ [])

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
        toExpr : Term → TC Term
        toExpr (def (quote _+_) xs) = getBinOp (quote _⊕_) xs
        toExpr (def (quote _*_) xs) = getBinOp (quote _⊗_) xs
        toExpr (def (quote _^_) xs) = getExp xs
        toExpr (def (quote -_) xs) = getUnOp (quote ⊝_) xs
        toExpr (def nm xs) = if (matchName +-nm nm) then ( getBinOp (quote _⊕_) xs) else
                          if (matchName *-nm nm) then ( getBinOp (quote _⊗_) xs) else
                          if (matchName ^-nm nm) then ( getExp xs) else
                          if (matchName -‿nm nm) then ( getUnOp (quote ⊝_) xs) else
                          pure (constExpr (def nm xs))
        toExpr v@(var x _) = pure $ Maybe.fromMaybe (constExpr v) (varExpr x)
        toExpr t = pure $ constExpr t

    callSolver : List String → Term → Term → TC (List (Arg Type))
    callSolver nms lhs rhs = do
      +-nm ← getName (quote _+_)
      *-nm ← getName (quote _*_)
      ^-nm ← getName (quote _^_)
      -‿nm ← getName (quote -_)
      lhs′ ← toExpr +-nm *-nm ^-nm -‿nm lhs
      rhs′ ← toExpr +-nm *-nm ^-nm -‿nm rhs
      pure $
        2 ⋯⟅∷⟆
        rng ⟨∷⟩
        natTerm numVars ⟨∷⟩
        vlams nms (quote _⊜_ ⟨ def ⟩ 2 ⋯⟅∷⟆ rng ⟨∷⟩ natTerm numVars ⟨∷⟩ lhs′ ⟨∷⟩ rhs′ ⟨∷⟩ []) ⟨∷⟩
        hlams nms (quote refl ⟨ def ⟩ 2 ⋯⟅∷⟆ rng ⟨∷⟩ 1 ⋯⟅∷⟆ []) ⟨∷⟩
        []
      where
      varExpr : ℕ → Maybe Term
      varExpr i with i ℕ.<? numVars
      ... | yes _ = just (var i [])
      ... | no _ = nothing
      open ToExpr varExpr

    constructSoln : Table → Term → Term → TC Term
    constructSoln t lhs rhs = do
      +-nm ← getName (quote _+_)
      *-nm ← getName (quote _*_)
      ^-nm ← getName (quote _^_)
      -‿nm ← getName (quote -_)
      lhs′ ← toExpr +-nm *-nm ^-nm -‿nm lhs
      rhs′ ← toExpr +-nm *-nm ^-nm -‿nm rhs
      pure $
        quote trans ⟨ def ⟩
          2 ⋯⟅∷⟆
          rng ⟨∷⟩
          3 ⋯⟅∷⟆
          (quote sym ⟨ def ⟩
              (2 ⋯⟅∷⟆
              rng ⟨∷⟩
              2 ⋯⟅∷⟆
              (quote Ops.correct ⟨ def ⟩ 2 ⋯⟅∷⟆ rng ⟨∷⟩ 1 ⋯⟅∷⟆ lhs′ ⟨∷⟩ ρ ⟨∷⟩ []) ⟨∷⟩
              []))
          ⟨∷⟩
          (quote Ops.correct ⟨ def ⟩ 2 ⋯⟅∷⟆ rng ⟨∷⟩ 1 ⋯⟅∷⟆ rhs′ ⟨∷⟩ ρ ⟨∷⟩ []) ⟨∷⟩
          []
      where
      varExpr : ℕ → Maybe Term
      varExpr i = Maybe.map (λ x → quote Ι ⟨ con ⟩ E⟅∷⟆ finTerm x ⟨∷⟩ []) (member i t)

      open ToExpr varExpr
      ρ : Term
      ρ = curriedTerm t

  toSoln : Term → TC Term
  toSoln t′ = go 0 id t′
    where
    go : ℕ → (List String → List String) → Term → TC Term
    go i k (def f (            lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = def (quote solve′) <$> callSolver i (k []) lhs rhs
    go i k (def f (    _ ∷ _ ∷ lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = def (quote solve′) <$> callSolver i (k []) lhs rhs
    go i k (def f (_ ∷ _ ∷ _ ∷ lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = def (quote solve′) <$> callSolver i (k []) lhs rhs
    go i k (pi a (abs s x)) = go (suc i) (k ∘ (s ∷_)) x
    go i k t = typeError (strErr "Malformed call to solve." ∷
                          strErr "Expected target type to be like: ∀ x y → x + y ≈ y + x." ∷
                          strErr "Instead: " ∷
                          termErr t′ ∷
                          [])

  listType : Term → TC Term
  listType t =
    checkType t (def (quote List) (1 ⋯⟅∷⟆ def (quote Carrier) (2 ⋯⟅∷⟆ rng ⟨∷⟩ []) ⟨∷⟩ [])) ⟨ bindTC ⟩ normalise

  checkRing : TC Term
  checkRing = checkType rng (def (quote AlmostCommutativeRing) (unknown ⟨∷⟩ unknown ⟨∷⟩ []))

  toSoln′ : Term  → Term → TC Term
  toSoln′ t′ xs′ = go [] t′ xs′
    where
    go′ : Table → Term → TC Term
    go′ i (def f (            lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = constructSoln (List.length i) i lhs rhs
    go′ i (def f (_ ∷ _ ∷     lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = constructSoln (List.length i) i lhs rhs
    go′ i (def f (_ ∷ _ ∷ _ ∷ lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = constructSoln (List.length i) i lhs rhs
    go′ _ _ = typeError (strErr "Malformed call to solveOver." ∷
                         strErr "Target type should be an equality like x + y ≈ y + x." ∷
                         strErr "Instead: " ∷
                         termErr xs′ ∷
                         [])

    go : Table → Term → Term → TC Term
    go t (con (quote List._∷_) (_ ∷ _ ∷ var i [] ⟨∷⟩ xs ⟨∷⟩ _)) ys = go (insert i t) xs ys
    go t (con (quote List.List.[]) _) xs = go′ t xs
    go i k t = typeError (strErr "Malformed call to solveOver." ∷
                          strErr "First argument should be a list of free variables." ∷
                          strErr "Instead: " ∷
                          termErr t′ ∷
                          [])
open Internal

-- This is the main macro you'll probably be using. Call it like this:
--
--   lemma : ∀ x y → x + y ≈ y + x
--   lemma = solve TypeRing
--
-- where TypRing is your implementation of AlmostCommutativeRing. (Find some
-- example implementations in Polynomial.Solver.Ring.AlmostCommutativeRing.Instances).
macro
  solve : Name → Term → TC ⊤
  solve rng′ hole = do
    rng ← checkRing (def rng′ [])
    commitTC
    soln ← inferType hole ⟨ bindTC ⟩ reduce ⟨ bindTC ⟩ toSoln rng
    commitTC
    unify hole soln

-- Use this macro when you want to solve something *under* a lambda. For example:
-- say you have a long proof, and you just want the solver to deal with an
-- intermediate step. Call it like so:
--
--   lemma₃ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
--   lemma₃ x y = begin
--     x + y * 1 + 3 ≈⟨ +-comm x (y * 1) ⟨ +-cong ⟩ refl ⟩
--     y * 1 + x + 3 ≈⟨ solveOver (x ∷ y ∷ []) Int.ring ⟩
--     3 + y + x     ≡⟨ refl ⟩
--     2 + 1 + y + x ∎
--
-- The first argument is the free variables, and the second is the
-- ring implementation (as before).
--
-- One thing to note here is that we need to be able to infer *both* sides of
-- the equality, which the normal equaltional reasoning combinators don't let you
-- do. You'll need the combinators defined in Relation.Binary.Reasoning.Inference.
-- These are just as powerful as the others, but have slightly better inference properties.

macro
  solveOver : Term → Name → Term → TC ⊤
  solveOver i′ rng′ hole = do
    rng ← checkRing (def rng′ [])
    commitTC
    i ← listType rng i′
    commitTC
    soln ← inferType hole ⟨ bindTC ⟩ reduce ⟨ bindTC ⟩ toSoln′ rng i
    commitTC
    unify hole soln
