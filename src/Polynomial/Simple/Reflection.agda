module Polynomial.Simple.Reflection where

open import Agda.Builtin.Reflection
open import Reflection
open import Function
open import Data.Unit using (⊤)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using (List; _∷_; []; foldr)

_>>=_ : {A B : Set} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

module Internal (rng : Term) where
  open import Polynomial.Simple.Solver renaming (solve to solve′)
  open import Data.String
  open import Relation.Nullary using (Dec; yes; no)
  import Data.Vec as Vec
  import Data.Fin as Fin
  open import Data.Maybe as Maybe using (Maybe; just; nothing)

  open import Data.Nat.Table

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

  curriedTerm : Table → Term
  curriedTerm = go zero
    where
    go : ℕ → Table → Term
    go k [] = quote Vec.[] ⟨ con ⟩ 2 ⋯⟅∷⟆ []
    go k (x ∷ xs) = quote Vec._∷_ ⟨ con ⟩ 2 ⋯⟅∷⟆ 1 ⋯⟅∷⟆ var (k ℕ.+ x) [] ⟨∷⟩ go (suc (k ℕ.+ x)) xs ⟨∷⟩ []

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

    module ToExpr (varExpr : ℕ → Maybe Term) where
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
        toExpr v@(var x _) = Maybe.fromMaybe (constExpr v) (varExpr x)
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
      varExpr : ℕ → Maybe Term
      varExpr i with i ℕ.<? numVars
      ... | yes _ = just (var i [])
      ... | no _ = nothing
      open ToExpr varExpr

    mkSolver′ : Table → Term → Term → Term
    mkSolver′ t lhs rhs =
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
      varExpr : ℕ → Maybe Term
      varExpr i = Maybe.map (λ x → quote Ι ⟨ con ⟩ E⟅∷⟆ finTerm x ⟨∷⟩ []) (member i t)

      open ToExpr varExpr
      ρ : Term
      ρ = curriedTerm t

  toSoln : Term → TC Term
  toSoln t′ = go 0 id t′
    where
    go : ℕ → (List String → List String) → Term → TC Term
    go i k (def f (            lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = returnTC $ quote solve′ ⟨ def ⟩ mkSolver i (k []) lhs rhs
    go i k (def f (    _ ∷ _ ∷ lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = returnTC $ quote solve′ ⟨ def ⟩ mkSolver i (k []) lhs rhs
    go i k (def f (_ ∷ _ ∷ _ ∷ lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = returnTC $ quote solve′ ⟨ def ⟩ mkSolver i (k []) lhs rhs
    go i k (pi a (abs s x)) = go (suc i) (k ∘ (s ∷_)) x
    go i k t = typeError (strErr "Malformed call to solve." ∷
                          strErr "Expected target type to be like: ∀ x y → x + y ≈ y + x." ∷
                          strErr "Instead: " ∷
                          termErr t′ ∷
                          [])

  listType : Term → TC Term
  listType t = do
    t′ ← normalise t
    checkType t′ (def (quote List) (1 ⋯⟅∷⟆ def (quote AlmostCommutativeRing.Carrier) (2 ⋯⟅∷⟆ rng ⟨∷⟩ []) ⟨∷⟩ []))

  checkRing : TC Term
  checkRing = checkType rng (def (quote AlmostCommutativeRing) (unknown ⟨∷⟩ unknown ⟨∷⟩ []))

  toSoln′ : Term  → Term → TC Term
  toSoln′ t′ xs′ = go [] t′ xs′
    where
    go′ : Table → Term → TC Term
    go′ i (def f (            lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = returnTC $ mkSolver′ (List.length i) i lhs rhs
    go′ i (def f (_ ∷ _ ∷     lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = returnTC $ mkSolver′ (List.length i) i lhs rhs
    go′ i (def f (_ ∷ _ ∷ _ ∷ lhs ⟨∷⟩ rhs ⟨∷⟩ [])) = returnTC $ mkSolver′ (List.length i) i lhs rhs
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
    _ ← commitTC
    inferType hole ⟨ bindTC ⟩ reduce ⟨ bindTC ⟩ toSoln rng ⟨ bindTC ⟩ unify hole

-- Use this macro when you want to solve something *under* a lambda. For example:
-- say you have a long proof, and you just want the solver to deal with an
-- intermediate step. Call it like so:
--
--   lemma₃ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
--   lemma₃ x y = begin
--     x + y * 1 + 3 ≈⟨ +-comm x (y * 1) ⟨ +-cong ⟩ refl ⟩
--     y * 1 + x + 3 ≋⟨ solveOver (x ∷ y ∷ []) Int.ring ⟩
--     3 + y + x     ≡⟨ refl ⟩
--     2 + 1 + y + x ∎
--
-- The first argument is the free variables, and the second is the
-- ring implementation (as before).
--
-- One thing to note here is that we need to be able to infer *both* sides of
-- the equality, which the normal equaltional reasoning combinators don't let you
-- do. You'll need a special combinator, defined in Relation.Binary.Reasoning.Inference.

macro
  solveOver : Term → Name → Term → TC ⊤
  solveOver i′ rng′ hole = do
    rng ← checkRing (def rng′ [])
    _ ← commitTC
    i ← listType rng i′
    _ ← commitTC
    inferType hole ⟨ bindTC ⟩ reduce ⟨ bindTC ⟩ toSoln′ rng i ⟨ bindTC ⟩ unify hole
