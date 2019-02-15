module Polynomial.Simple.Reflection where

open import Reflection
open import Function
open import Data.Unit using (⊤)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.List as List using (List; _∷_; []; foldr)

module Internal where
  open import Polynomial.Simple.Solver renaming (solve to solve′)
  open import Data.String
  open import Relation.Nullary using (Dec; yes; no)

  -- Some patterns to decrease verbosity
  infixr 5 ⟨_⟩∷_ ⟅_⟆∷_
  pattern ⟨_⟩∷_ x xs = arg (arg-info visible relevant) x ∷ xs
  pattern ⟅_⟆∷_ x xs = arg (arg-info hidden relevant) x ∷ xs

  natTerm : ℕ → Term
  natTerm zero = quote zero ⟨ con ⟩ []
  natTerm (suc i) = quote suc ⟨ con ⟩ ⟨ natTerm i ⟩∷ []

  import Data.Fin as Fin

  finTerm : ℕ → Term
  finTerm zero = quote Fin.zero ⟨ con ⟩ ⟅ unknown ⟆∷ []
  finTerm (suc i) = quote Fin.suc ⟨ con ⟩ ⟅ unknown ⟆∷ ⟨ finTerm i ⟩∷ []

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



  module WithRefl (varExpr : ℕ → Term) where
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

      getExp : ℕ → List (Arg Term) → Term
      getExp i (⟨ x ⟩∷ ⟨ y ⟩∷ []) = quote _⊛_ ⟨ con ⟩ ⟅ i ⋯⟆∷ ⟨ toExpr i x ⟩∷ ⟨ y ⟩∷ []
      getExp i (x ∷ xs) = getExp i xs
      getExp _ _ = unknown

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
      toExpr i (def (quote AlmostCommutativeRing._+_) xs) = getBinOp i (quote _⊕_) xs
      toExpr i (def (quote AlmostCommutativeRing._*_) xs) = getBinOp i (quote _⊗_) xs
      toExpr i (def (quote AlmostCommutativeRing._^_) xs) = getExp i xs
      toExpr i (def (quote AlmostCommutativeRing.-_) xs) = getUnOp i (quote ⊝_) xs
      toExpr i v@(var x args) with suc x ℕ.≤? i
      ... | yes p = varExpr x
      ... | no ¬p = constExpr i v
      {-# CATCHALL #-}
      toExpr i t = constExpr i t


  hlams : List String → Term → Term
  hlams vs xs = foldr (λ v vs → lam hidden (abs v vs)) xs vs

  vlams : List String → Term → Term
  vlams vs xs = foldr (λ v vs → lam visible (abs v vs)) xs vs

  mkSolver : List String → Name → ℕ → Term → Term → List (Arg Type)
  mkSolver nms rng i lhs rhs =
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
            ⟨ WithRefl.toExpr (λ x → var x []) i lhs ⟩∷
            ⟨ WithRefl.toExpr (λ x → var x []) i rhs ⟩∷
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
    go i k (def f (            ⟨ lhs ⟩∷ ⟨ rhs ⟩∷ [])) = quote solve′ ⟨ def ⟩ mkSolver (k []) rng i lhs rhs
    go i k (def f (    _ ∷ _ ∷ ⟨ lhs ⟩∷ ⟨ rhs ⟩∷ [])) = quote solve′ ⟨ def ⟩ mkSolver (k []) rng i lhs rhs
    go i k (def f (_ ∷ _ ∷ _ ∷ ⟨ lhs ⟩∷ ⟨ rhs ⟩∷ [])) = quote solve′ ⟨ def ⟩ mkSolver (k []) rng i lhs rhs
    go i k (pi a (abs s x)) = go (suc i) (k ∘ (s ∷_)) x
    go i k t = unknown

  open import Data.Vec as Vec using (_∷_; [])

  toVecTerm : ℕ → Term
  toVecTerm = go zero
    where
    go : ℕ → ℕ → Term
    go k zero = quote Vec.[] ⟨ con ⟩ ⟅ unknown ⟆∷ ⟅ unknown ⟆∷ []
    go k (suc i) = quote Vec._∷_ ⟨ con ⟩ ⟅ unknown ⟆∷ ⟅ unknown ⟆∷ ⟅ unknown ⟆∷ ⟨ var k [] ⟩∷ ⟨ go (suc k) i ⟩∷ []

  mkSolver′ : Name → ℕ → Term → Term → Term
  mkSolver′ rng i lhs rhs = quote AlmostCommutativeRing.trans ⟨ def ⟩
                              ⟅ unknown ⟆∷
                              ⟅ unknown ⟆∷
                              ⟨ def rng [] ⟩∷
                              ⟅ unknown ⟆∷
                              ⟅ unknown ⟆∷
                              ⟅ unknown ⟆∷
                              ⟨ quote AlmostCommutativeRing.sym ⟨ def ⟩
                                  ⟅ unknown ⟆∷
                                  ⟅ unknown ⟆∷
                                  ⟨ def rng [] ⟩∷
                                  ⟅ unknown ⟆∷
                                  ⟅ unknown ⟆∷
                                  ⟨ quote Ops.correct ⟨ def ⟩
                                      ⟅ unknown ⟆∷
                                      ⟅ unknown ⟆∷
                                      ⟨ def rng [] ⟩∷
                                      ⟅ unknown ⟆∷
                                      ⟨ WithRefl.toExpr (λ x → quote Ι ⟨ con ⟩ ⟅ i ⋯⟆∷ ⟨ finTerm x ⟩∷ []) i lhs ⟩∷
                                      ⟨ ρ ⟩∷
                                      []
                                  ⟩∷
                                  []
                              ⟩∷
                              ⟨ quote Ops.correct ⟨ def ⟩
                                  ⟅ unknown ⟆∷
                                  ⟅ unknown ⟆∷
                                  ⟨ def rng [] ⟩∷
                                  ⟅ unknown ⟆∷
                                  ⟨ WithRefl.toExpr (λ x → quote Ι ⟨ con ⟩ ⟅ i ⋯⟆∷ ⟨ finTerm x ⟩∷ []) i rhs ⟩∷
                                  ⟨ ρ ⟩∷
                                  []
                              ⟩∷
                              []
    where
    ρ : Term
    ρ = toVecTerm i


  toSoln′ : ℕ → Name → Term → Term
  toSoln′ i rng (def f (⟨ lhs ⟩∷ ⟨ rhs ⟩∷ []))             = mkSolver′ rng i lhs rhs
  toSoln′ i rng (def f (_ ∷ _ ∷ ⟨ lhs ⟩∷ ⟨ rhs ⟩∷ []))     = mkSolver′ rng i lhs rhs
  toSoln′ i rng (def f (_ ∷ _ ∷ _ ∷ ⟨ lhs ⟩∷ ⟨ rhs ⟩∷ [])) = mkSolver′ rng i lhs rhs
  toSoln′ _ _ _ = unknown

open Internal
open import Agda.Builtin.Reflection
macro
  solve : Name → Term → TC ⊤
  solve rng hole =
    inferType hole ⟨ bindTC ⟩ reduce ⟨ bindTC ⟩ unify hole ∘ toSoln rng

_>>=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_>>=_ = bindTC

macro
  solveFor : ℕ → Name → Term → TC ⊤
  solveFor i rng hole = do
    hole′ ← inferType hole >>= reduce
    let res = toSoln′ i rng hole′
    unify hole res -- ⟨ catchTC ⟩ typeError (termErr res ∷ [])
