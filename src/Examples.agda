module Examples where
--------------------------------------------------------------------------------

-- First, we need to overload the literals Agda uses for numbers.
-- This bit isn't necessary if you're just using ℕ, or if you
-- construct your type directly. We only really do it here so that
-- we can use different numeric types in the same file.

open import Agda.Builtin.FromNat
open import Data.Nat as ℕ using (ℕ)
open import Data.Integer as ℤ using (ℤ)

instance
  numberNat : Number ℕ
  numberNat = Data.Nat.Literals.number
    where import Data.Nat.Literals

instance
  numberInt : Number ℤ
  numberInt = Data.Integer.Literals.number
    where import Data.Integer.Literals

--------------------------------------------------------------------------------

-- These are the minimal imports you need to use the "simple" version
-- of the reflection-based solver.
open import Polynomial.Simple.AlmostCommutativeRing           -- The particular algebra we use
open import Polynomial.Simple.AlmostCommutativeRing.Instances -- Some instances for that algebra
open import Polynomial.Simple.Reflection                      -- The reflection-based interface

--------------------------------------------------------------------------------

-- First, some automatic proofs for ℤ (integers).
module IntExamples where
  -- We can use any of the operators from an "Almost Commutative Ring"
  open AlmostCommutativeRing Int.ring

  -- The (reflection-based) solver works by first figuring out the goal,
  -- and then filling in the relevant proofs.
  lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 3 + 1 + y + x + - 1
  lemma₁ = solve Int.ring

  lemma₂ : ∀ x y → (x + y) ^ 2 ≈ x ^ 2 + 2 * x * y + y ^ 2
  lemma₂ = solve Int.ring

  -- It's possible to have non-literals in the expression, as well.
  n : ℤ
  n = 4

  lemma₃ : ∀ x y → n * (y + x) ≈ 4 * x + 4 * y
  lemma₃ = solve Int.ring

--------------------------------------------------------------------------------
-- The solver also works with ℕ, even though it asks for rings!
module NatExamples where
  open AlmostCommutativeRing Nat.ring

  lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
  lemma₁ = solve Nat.ring

--------------------------------------------------------------------------------
-- It also gives "step-by-step", human-readable output:
module TracedExamples where
  import Data.Nat.Show
  open import Data.List using (_∷_; [])
  open import Agda.Builtin.Nat using (_==_)
  open import Relation.Traced Nat.ring _==_ Data.Nat.Show.show public
  open AlmostCommutativeRing tracedRing
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)

  lemma : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x
  lemma = solve tracedRing


  explained
    : showProof (lemma "x" "y") ≡ "x + (y + 3)"
                                ∷ "    ={ +-comm(x, y + 3) }"
                                ∷ "y + 3 + x"
                                ∷ "    ={ +-comm(y, 3) }"
                                ∷ "3 + y + x"
                                ∷ []
  explained = ≡.refl

--------------------------------------------------------------------------------
-- Previously, you had to construct the expression you wanted to solve twice:
-- once in the type signature, and again using the special solver syntax.
--
-- This is difficult to learn, and error-prone: if I change an x + y somewhere
-- to a y + x, I *also* have to change the proofs now! The reflection-based
-- solver will automatically construct the new proof.
module OldSolver where
  open import Relation.Binary.PropositionalEquality
  open import Data.Nat
  open import Data.Nat.Solver using (module +-*-Solver)
  open +-*-Solver

  lemma : ∀ x y → x + y * 1 + 3 ≡ 2 + 1 + y + x
  lemma = +-*-Solver.solve 2 (λ x y → x :+ y :* con 1 :+ con 3 := con 2 :+ con 1 :+ y :+ x) refl
