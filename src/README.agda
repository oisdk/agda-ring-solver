-- ------------------------------------------------------------------------------------------------------
-- | ███████╗ ██████╗ ██╗     ██╗   ██╗██╗███╗   ██╗ ██████╗     ██████╗ ██╗███╗   ██╗ ██████╗ ███████╗ |
-- | ██╔════╝██╔═══██╗██║     ██║   ██║██║████╗  ██║██╔════╝     ██╔══██╗██║████╗  ██║██╔════╝ ██╔════╝ |
-- | ███████╗██║   ██║██║     ██║   ██║██║██╔██╗ ██║██║  ███╗    ██████╔╝██║██╔██╗ ██║██║  ███╗███████╗ |
-- | ╚════██║██║   ██║██║     ╚██╗ ██╔╝██║██║╚██╗██║██║   ██║    ██╔══██╗██║██║╚██╗██║██║   ██║╚════██║ |
-- | ███████║╚██████╔╝███████╗ ╚████╔╝ ██║██║ ╚████║╚██████╔╝    ██║  ██║██║██║ ╚████║╚██████╔╝███████║ |
-- | ╚══════╝ ╚═════╝ ╚══════╝  ╚═══╝  ╚═╝╚═╝  ╚═══╝ ╚═════╝     ╚═╝  ╚═╝╚═╝╚═╝  ╚═══╝ ╚═════╝ ╚══════╝ |
-- |                                                                                                    |
-- |                         ██╗███╗   ██╗     █████╗  ██████╗ ██████╗  █████╗                          |
-- |                         ██║████╗  ██║    ██╔══██╗██╔════╝ ██╔══██╗██╔══██╗                         |
-- |                         ██║██╔██╗ ██║    ███████║██║  ███╗██║  ██║███████║                         |
-- |                         ██║██║╚██╗██║    ██╔══██║██║   ██║██║  ██║██╔══██║                         |
-- |                         ██║██║ ╚████║    ██║  ██║╚██████╔╝██████╔╝██║  ██║                         |
-- |                         ╚═╝╚═╝  ╚═══╝    ╚═╝  ╚═╝ ╚═════╝ ╚═════╝ ╚═╝  ╚═╝                         |
-- ------------------------------------------------------------------------------------------------------
--
--                                         Donnacha Oisín Kidney
--                                            22 January 2019

module README where

-- This contains the worked-through source code for:
--
--     "Automatically And Efficiently Illustrating Polynomial Equalities in Agda"
--
--     We present a new library which automates the construction of equivalence
--     proofs between polynomials over commutative rings and semirings in the
--     programming language Agda. It is asymptotically faster than Agda's existing
--     solver. We use Agda's reflection machinery to provide a simple interface to
--     the solver, and demonstrate an interesting use of the constructed relations:
--     step-by-step solutions.
--
-- Which is (at time of writing) a work-in-progress.
--
-- This code is available on github:
--     https://github.com/oisdk/agda-ring-solver
--
-- As is the paper:
--     https://github.com/oisdk/agda-ring-solver-report
--
--------------------------------------------------------------------------------
-- There are 3 main contributions in this library:                            --
--                                                                            --
--   * A solver for polynomials over "almost commutative rings".              --
--         Agda already has one these in the standard library, but this one   --
--         is much more efficient. "Almost commutative rings" encapsulates a  --
--         bunch of things, including ℕ.                                      --
--                                                                            --
--   * A reflection-based interface.                                          --
--         Not many people used the old solver, mainly (I think) because the  --
--         interface was difficult and irritating. This library provides a    --
--         super-simple interface using reflection.                           --
--                                                                            --
--   * An implementation of "step-by-step solutions".                         --
--         I don't know a huge amount about computer algebra systems, but I   --
--         have used Wolfram Alpha countless times (especially when I was in  --
--         school) to help with basic maths. I was able to get this solver to --
--         produce step-by-step solutions, and learned something about the    --
--         theory behind them along the way.                                  --
--------------------------------------------------------------------------------
--
-- ███████╗██╗   ██╗██╗     ██╗          ██████╗ ██████╗ ██████╗ ███████╗
-- ██╔════╝██║   ██║██║     ██║         ██╔════╝██╔═══██╗██╔══██╗██╔════╝
-- █████╗  ██║   ██║██║     ██║         ██║     ██║   ██║██║  ██║█████╗   ███████████████████████████╗
-- ██╔══╝  ██║   ██║██║     ██║         ██║     ██║   ██║██║  ██║██╔══╝   ╚════════════════════════██║
-- ██║     ╚██████╔╝███████╗███████╗    ╚██████╗╚██████╔╝██████╔╝███████╗                          ██║
-- ╚═╝      ╚═════╝ ╚══════╝╚══════╝     ╚═════╝ ╚═════╝ ╚═════╝ ╚══════╝                          ██║
--                                                                                                 ██║
-- ██████╗ ███████╗███╗   ██╗ ██████╗██╗  ██╗███╗   ███╗ █████╗ ██████╗ ██╗  ██╗███████╗           ██║
-- ██╔══██╗██╔════╝████╗  ██║██╔════╝██║  ██║████╗ ████║██╔══██╗██╔══██╗██║ ██╔╝██╔════╝           ██║
-- ██████╔╝█████╗  ██╔██╗ ██║██║     ███████║██╔████╔██║███████║██████╔╝█████╔╝ ███████╗ ███████╗  ██║
-- ██╔══██╗██╔══╝  ██║╚██╗██║██║     ██╔══██║██║╚██╔╝██║██╔══██║██╔══██╗██╔═██╗ ╚════██║ ╚════██║  ██║
-- ██████╔╝███████╗██║ ╚████║╚██████╗██║  ██║██║ ╚═╝ ██║██║  ██║██║  ██║██║  ██╗███████║      ██║  ██║
-- ╚═════╝ ╚══════╝╚═╝  ╚═══╝ ╚═════╝╚═╝  ╚═╝╚═╝     ╚═╝╚═╝  ╚═╝╚═╝  ╚═╝╚═╝  ╚═╝╚══════╝      ██║  ██║
--                                                                                            ██║  ██║
-- ███████╗██╗  ██╗ █████╗ ███╗   ███╗██████╗ ██╗     ███████╗███████╗                        ██║  ██║
-- ██╔════╝╚██╗██╔╝██╔══██╗████╗ ████║██╔══██╗██║     ██╔════╝██╔════╝                        ██║  ██║
-- █████╗   ╚███╔╝ ███████║██╔████╔██║██████╔╝██║     █████╗  ███████╗ ████████████████████╗  ██║  ██║
-- ██╔══╝   ██╔██╗ ██╔══██║██║╚██╔╝██║██╔═══╝ ██║     ██╔══╝  ╚════██║ ╚═════════════════██║  ██║  ██║
-- ███████╗██╔╝ ██╗██║  ██║██║ ╚═╝ ██║██║     ███████╗███████╗███████║                   ██║  ██║  ██║
-- ╚══════╝╚═╝  ╚═╝╚═╝  ╚═╝╚═╝     ╚═╝╚═╝     ╚══════╝╚══════╝╚══════╝                   ██║  ██║  ██║
--                                                                                       ██║  ██║  ██║
--------------------------------------------------------------------------------         ██║  ██║  ██║
-- You can ignore this bit! We're just overloading the literals Agda uses for --         ██║  ██║  ██║
-- numbers This bit isn't necessary if you're just using Nats, or if you      --         ██║  ██║  ██║
-- construct your type directly. We only really do it here so that we can use --         ██║  ██║  ██║
-- different numeric types in the same file.                                  --         ██║  ██║  ██║
                                                                              --         ██║  ██║  ██║
open import Agda.Builtin.FromNat                                              --         ██║  ██║  ██║
open import Agda.Builtin.Nat using (Nat)                                      --         ██║  ██║  ██║
open import Agda.Builtin.Int using (Int)                                      --         ██║  ██║  ██║
                                                                              --         ██║  ██║  ██║
instance                                                                      --         ██║  ██║  ██║
  numberNat : Number Nat                                                      --         ██║  ██║  ██║
  numberNat = Data.Nat.Literals.number                                        --         ██║  ██║  ██║
    where import Data.Nat.Literals                                            --         ██║  ██║  ██║
                                                                              --         ██║  ██║  ██║
instance                                                                      --         ██║  ██║  ██║
  numberInt : Number Int                                                      --         ██║  ██║  ██║
  numberInt = Data.Integer.Literals.number                                    --         ██║  ██║  ██║
    where import Data.Integer.Literals                                        --         ██║  ██║  ██║
                                                                              --         ██║  ██║  ██║
--------------------------------------------------------------------------------         ██║  ██║  ██║
-- Imports!                                                                   --         ██║  ██║  ██║
                                                                              --         ██║  ██║  ██║
open import Polynomial.Simple.AlmostCommutativeRing                           --         ██║  ██║  ██║
open import Polynomial.Simple.AlmostCommutativeRing.Instances                 --         ██║  ██║  ██║
open import Polynomial.Simple.Reflection                                      --         ██║  ██║  ██║
--------------------------------------------------------------------------------         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--                           8888888888',8888'                                --         ██║  ██║  ██║
--                                  ,8',8888'                                 --         ██║  ██║  ██║
--                                 ,8',8888'                                  --         ██║  ██║  ██║
--                                ,8',8888'                                   --         ██║  ██║  ██║
--                               ,8',8888'                                    --         ██║  ██║  ██║
--                              ,8',8888'                                     --         ██║  ██║  ██║
--                             ,8',8888'                                      --         ██║  ██║  ██║
--                            ,8',8888'                                       --         ██║  ██║  ██║
--                           ,8',8888'                                        --         ██║  ██║  ██║
--                          ,8',8888888888888                                 --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--------------------------------------------------------------------------------         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
module IntExamples where                                                      --         ██║  ██║  ██║
  open AlmostCommutativeRing Int.ring                                         --         ██║  ██║  ██║
  -- Everything is automatic: you just ask Agda to solve it and it does!      --     ██╗ ██║  ██║  ██║
  lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 3 + 1 + y + x + - 1                        --   ████║ ██║  ██║  ██║
  lemma₁ = solve Int.ring                                                     -- ██████████║  ██║  ██║
                                                                              --   ████╔═██║  ██║  ██║
  lemma₂ : ∀ x y → (x + y) ^ 2 ≈ x ^ 2 + 2 * x * y + y ^ 2                    --     ██║ ██║  ██║  ██║
  lemma₂ = solve Int.ring                                                     --     ╚═╝ ██║  ██║  ██║
                                                                              --         ██║  ██║  ██║
  open import Relation.Binary.EqReasoning setoid                              --         ██║  ██║  ██║
  open import Function                                                        --         ██║  ██║  ██║
  open import Relation.Binary.Reasoning.Inference _≈_ refl trans              --         ██║  ██║  ██║
                                                                              --         ██║  ██║  ██║
  -- It can interact with manual proofs as well.                              --         ██║  ██║  ██║
  lemma₃ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x                              --         ██║  ██║  ██║
  lemma₃ x y = begin                                                          --         ██║  ██║  ██║
    x + y * 1 + 3 ≈⟨ +-comm x (y * 1) ⟨ +-cong ⟩ refl ⟩                       --         ██║  ██║  ██║
    y * 1 + x + 3 ≋⟨ solveFor 2 Int.ring ⟩                                    --         ██║  ██║  ██║
    3 + y + x     ≡⟨ refl ⟩                                                   --         ██║  ██║  ██║
    2 + 1 + y + x ∎                                                           --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--------------------------------------------------------------------------------         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--                          b.             8                                  --         ██║  ██║  ██║
--                          888o.          8                                  --         ██║  ██║  ██║
--                          Y88888o.       8                                  --         ██║  ██║  ██║
--                          .`Y888888o.    8                                  --         ██║  ██║  ██║
--                          8o. `Y888888o. 8                                  --         ██║  ██║  ██║
--                          8`Y8o. `Y88888o8                                  --         ██║  ██║  ██║
--                          8   `Y8o. `Y8888                                  --         ██║  ██║  ██║
--                          8      `Y8o. `Y8                                  --         ██║  ██║  ██║
--                          8         `Y8o.`                                  --         ██║  ██║  ██║
--                          8            `Yo                                  --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--------------------------------------------------------------------------------         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
module NatExamples where                                                      --         ██║  ██║  ██║
  open AlmostCommutativeRing Nat.ring                                         --     ██╗ ██║  ██║  ██║
  -- The solver is flexible enough to work with Nats (even though it asks     --   ████║ ██║  ██║  ██║
  -- for rings!)                                                              -- ██████████║  ██║  ██║
  lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x                              --   ████╔═██║  ██║  ██║
  lemma₁ = solve Nat.ring                                                     --     ██║ ██║  ██║  ██║
--                                                                            --     ╚═╝ ██║  ██║  ██║
--------------------------------------------------------------------------------         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--             8888888 8888888888 8 8888        8 8 8888888888                --         ██║  ██║  ██║
--                   8 8888       8 8888        8 8 8888                      --         ██║  ██║  ██║
--                   8 8888       8 8888        8 8 8888                      --         ██║  ██║  ██║
--                   8 8888       8 8888        8 8 8888                      --         ██║  ██║  ██║
--                   8 8888       8 8888        8 8 888888888888              --         ██║  ██║  ██║
--                   8 8888       8 8888        8 8 8888                      --         ██║  ██║  ██║
--                   8 8888       8 8888888888888 8 8888                      --         ██║  ██║  ██║
--                   8 8888       8 8888        8 8 8888                      --         ██║  ██║  ██║
--                   8 8888       8 8888        8 8 8888                      --         ██║  ██║  ██║
--                   8 8888       8 8888        8 8 888888888888              --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--                 ,o888888o.     8 8888         8 888888888o.                --         ██║  ██║  ██║
--              . 8888     `88.   8 8888         8 8888    `^888.             --         ██║  ██║  ██║
--             ,8 8888       `8b  8 8888         8 8888        `88.           --         ██║  ██║  ██║
--             88 8888        `8b 8 8888         8 8888         `88           --         ██║  ██║  ██║
--             88 8888         88 8 8888         8 8888          88           --         ██║  ██║  ██║
--             88 8888         88 8 8888         8 8888          88           --         ██║  ██║  ██║
--             88 8888        ,8P 8 8888         8 8888         ,88           --         ██║  ██║  ██║
--             `8 8888       ,8P  8 8888         8 8888        ,88'           --         ██║  ██║  ██║
--              ` 8888     ,88'   8 8888         8 8888    ,o88P'             --         ██║  ██║  ██║
--                 `8888888P'     8 888888888888 8 888888888P'                --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--             `8.`888b                 ,8' .8.   `8.`8888.      ,8'          --         ██║  ██║  ██║
--              `8.`888b               ,8' .888.   `8.`8888.    ,8'           --         ██║  ██║  ██║
--               `8.`888b             ,8' :88888.   `8.`8888.  ,8'            --         ██║  ██║  ██║
--                `8.`888b     .b    ,8' . `88888.   `8.`8888.,8'             --         ██║  ██║  ██║
--                 `8.`888b    88b  ,8' .8. `88888.   `8.`88888'              --         ██║  ██║  ██║
--                  `8.`888b .`888b,8' .8`8. `88888.   `8. 8888               --         ██║  ██║  ██║
--                   `8.`888b8.`8888' .8' `8. `88888.   `8 8888               --         ██║  ██║  ██║
--                    `8.`888`8.`88' .8'   `8. `88888.   8 8888               --         ██║  ██║  ██║
--                     `8.`8' `8,`' .888888888. `88888.  8 8888               --         ██║  ██║  ██║
--                      `8.`   `8' .8'       `8. `88888. 8 8888               --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--------------------------------------------------------------------------------         ██║  ██║  ██║
-- Previously, you had to construct the expression you wanted to solve twice: --         ██║  ██║  ██║
-- once in the type signature, and again using the special solver syntax.     --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
-- This is difficult to learn, and error-prone: if I change an x + y          --         ██║  ██║  ██║
-- somewhere to a y + x, I *also* have to change the proofs now! The          --         ██║  ██║  ██║
-- reflection-based solver will automatically construct the new proof.        --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
module OldSolver where                                                        --         ██║  ██║  ██║
  open import Relation.Binary.PropositionalEquality                           --         ██║  ██║  ██║
  open import Data.Nat                                                        --         ██║  ██║  ██║
  open import Data.Nat.Solver using (module +-*-Solver)                       --         ██║  ██║  ██║
  open +-*-Solver                                                             --         ██║  ██║  ██║
                                                                              --     ██╗ ██║  ██║  ██║
  lemma : ∀ x y → x + y * 1 + 3 ≡ 2 + 1 + y + x                               --   ████║ ██║  ██║  ██║
  lemma = +-*-Solver.solve 2                                                  -- ██████████║  ██║  ██║
    (λ x y → x :+ y :* con 1 :+ con 3 := con 2 :+ con 1 :+ y :+ x) refl       --   ████╔═██║  ██║  ██║
--                                                                            --     ██║ ██║  ██║  ██║
--------------------------------------------------------------------------------     ╚═╝ ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--          d888888o.   8888888 8888888888 8 8888888888   8 888888888o        --         ██║  ██║  ██║
--        .`8888:' `88.       8 8888       8 8888         8 8888    `88.      --         ██║  ██║  ██║
--        8.`8888.   Y8       8 8888       8 8888         8 8888     `88      --         ██║  ██║  ██║
--        `8.`8888.           8 8888       8 8888         8 8888     ,88      --         ██║  ██║  ██║
--         `8.`8888.          8 8888       8 888888888888 8 8888.   ,88'      --         ██║  ██║  ██║
--          `8.`8888.         8 8888       8 8888         8 888888888P'       --         ██║  ██║  ██║
--           `8.`8888.        8 8888       8 8888         8 8888              --         ██║  ██║  ██║
--       8b   `8.`8888.       8 8888       8 8888         8 8888              --         ██║  ██║  ██║
--       `8b.  ;8.`8888       8 8888       8 8888         8 8888              --         ██║  ██║  ██║
--        `Y8888P ,88P'       8 8888       8 888888888888 8 8888              --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--                      8 888888888o   `8.`8888.      ,8'                     --         ██║  ██║  ██║
--                      8 8888    `88.  `8.`8888.    ,8'                      --         ██║  ██║  ██║
--                      8 8888     `88   `8.`8888.  ,8'                       --         ██║  ██║  ██║
--                      8 8888     ,88    `8.`8888.,8'                        --         ██║  ██║  ██║
--                      8 8888.   ,88'     `8.`88888'                         --         ██║  ██║  ██║
--                      8 8888888888        `8. 8888                          --         ██║  ██║  ██║
--                      8 8888    `88.       `8 8888                          --         ██║  ██║  ██║
--                      8 8888      88        8 8888                          --         ██║  ██║  ██║
--                      8 8888    ,88'        8 8888                          --         ██║  ██║  ██║
--                      8 888888888P          8 8888                          --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--          d888888o.   8888888 8888888888 8 8888888888   8 888888888o        --         ██║  ██║  ██║
--        .`8888:' `88.       8 8888       8 8888         8 8888    `88.      --         ██║  ██║  ██║
--        8.`8888.   Y8       8 8888       8 8888         8 8888     `88      --         ██║  ██║  ██║
--        `8.`8888.           8 8888       8 8888         8 8888     ,88      --         ██║  ██║  ██║
--         `8.`8888.          8 8888       8 888888888888 8 8888.   ,88'      --         ██║  ██║  ██║
--          `8.`8888.         8 8888       8 8888         8 888888888P'       --         ██║  ██║  ██║
--           `8.`8888.        8 8888       8 8888         8 8888              --         ██║  ██║  ██║
--       8b   `8.`8888.       8 8888       8 8888         8 8888              --         ██║  ██║  ██║
--       `8b.  ;8.`8888       8 8888       8 8888         8 8888              --         ██║  ██║  ██║
--        `Y8888P ,88P'       8 8888       8 888888888888 8 8888              --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
--------------------------------------------------------------------------------         ██║  ██║  ██║
-- Don't understand why something works? Wanna get it explained to you? Now   --         ██║  ██║  ██║
-- you can! The solver can generate step-by-step, human-readable solutions    --         ██║  ██║  ██║
-- for learning purposes.                                                     --         ██║  ██║  ██║
--                                                                            --         ██║  ██║  ██║
module TracedExamples where                                                   --         ██║  ██║  ██║
  import Data.Nat.Show                                                        --         ██║  ██║  ██║
  open import Data.List using (_∷_; [])                                       --         ██║  ██║  ██║
  open import EqBool                                                          --         ██║  ██║  ██║
  open import Relation.Traced Nat.ring  Data.Nat.Show.show public             --         ██║  ██║  ██║
  open AlmostCommutativeRing tracedRing                                       --         ██║  ██║  ██║
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)          --         ██║  ██║  ██║
                                                                              --         ██║  ██║  ██║
  lemma : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x                               --         ██║  ██║  ██║
  lemma = solve tracedRing                                                    --         ██║  ██║  ██║
                                                                              --      ██╗██║  ██║  ██║
  explained                                                                   --    ████║██║  ██║  ██║
    : showProof (lemma "x" "y") ≡ "x + y + 3"                                 --  █████████║  ██║  ██║
                                ∷ "    ={ +-comm(x, y + 3) }"                 --    ████╔══╝  ██║  ██║
                                ∷ "y + 3 + x"                                 --      ██║     ██║  ██║
                                ∷ "    ={ +-comm(y, 3) }"                     --      ╚═╝     ██║  ██║
                                ∷ "3 + y + x"                                 --              ██║  ██║
                                ∷ []                                          --              ██║  ██║
  explained = ≡.refl                                                          --              ██║  ██║
--------------------------------------------------------------------------------              ██║  ██║
--                                                                            --              ██║  ██║
-- The new solver uses a sparse representation, which is much faster than the --              ██║  ██║
-- dense one the old solver used. The following graph shows the time (in      --              ██║  ██║
-- seconds) to prove that:                                                    --              ██║  ██║
--                                                                            --              ██║  ██║
--     (1 + x₁¹ + x₂² + x₃³ + x₄⁴ + x₅⁵)ᵈ                                     --              ██║  ██║
--                                                                            --              ██║  ██║
-- is equal to its expanded form. (to run the benchmarks yourself, run the    --              ██║  ██║
-- run_benchmarks.py file. You'll need python 3 and sympy.)                   --              ██║  ██║
--                                                                            --              ██║  ██║
-- 540 |  * = old                                                       *     --              ██║  ██║
-- 525 |  + = new                                                       *     --              ██║  ██║
-- 510 |                                                                *     --              ██║  ██║
-- 495 |                                                                *     --              ██║  ██║
-- 480 |                                                                *     --              ██║  ██║
-- 465 |                                                               *      --              ██║  ██║
-- 450 |                                                               *      --              ██║  ██║
-- 435 |                                                               *      --              ██║  ██║
-- 420 |                                                              *       --              ██║  ██║
-- 405 |                                                              *       --              ██║  ██║
-- 390 |                                                              *       --              ██║  ██║
-- 375 |                                                             *        --              ██║  ██║
-- 360 |                                                             *        --              ██║  ██║
-- 345 |                                                             *        --              ██║  ██║
-- 330 |                                                            *         --              ██║  ██║
-- 315 |                                                            *         --              ██║  ██║
-- 300 |                                                            *         --              ██║  ██║
-- 285 |                                                           *          --              ██║  ██║
-- 270 |                                                           *          --              ██║  ██║
-- 255 |                                                           *          --              ██║  ██║
-- 240 |                                                          *           --           ██╗██║  ██║
-- 225 |                                                          *           --         ████║██║  ██║
-- 210 |                                                          *           --       █████████║  ██║
-- 195 |                                                         *            --         ████╔══╝  ██║
-- 180 |                                                         *            --           ██║     ██║
-- 165 |                                                         *            --           ╚═╝     ██║
-- 150 |                                                        *             --                   ██║
-- 135 |                                                        *             --                   ██║
-- 120 |                                                        *             --                   ██║
-- 105 |                                                       *              --                   ██║
--  90 |                                                      *               --                   ██║
--  75 |                                                     *                --                   ██║
--  60 |                                                   **                 --                   ██║
--  45 |                                                 **                   --                   ██║
--  30 |                                               **           +++++     --                   ██║
--  15 |                                          *****    +++++++++          --                   ██║
--   0 | *****************************************+++++++++                   --                   ██║
--     ------------------------------------------------------------------     --                   ██║
--   d = 1        2        3        4        5        6        7        8     --                   ██║
--------------------------------------------------------------------------------                   ██║
--                                                                                                 ██║
--                                 ██████████████████████████████████████████████████████████████████║
--                                 ██╔═══════════════════════════════════════════════════════════════╝
--                             ██████████╗
--                               ██████╔═╝
--                                 ██╔═╝
--                                 ╚═╝
--
-- * How does it work? Why is it fast?
--       The solver works by converting expressions to "Horner Normal Form".
--       This representation is special: x + y is represented in the same way
--       as y + x. This is what lets us check that two expressions are equal.
--       The implementation here is *sparse*, also, which is why it's faster
--       than the old implementation.
--
--       Want to learn more? Then this is the place for you:
import Polynomial.NormalForm
--
-- * Prove it!
--       The type of proofs we need are *homomorphisms*. They basically mean
--       that the operations on the normal form correspond to the operations
--       on expressions. Also, we don't use propositional equality: we use
--       any equivalence relation the user supplies.
--
--       Don't believe me? Check it out:
import Polynomial.Homomorphism
--
-- * How do I use it?
--       Copy the examples above! For the full solver, check out:
import Polynomial.Solver
--
-- * Wait! Don't!
--       The "full" solver lets you use different types for the coefficient
--       and carrier. You probably don't want that, unless you need the extra
--       efficiency. You'll want the *simple* solver:
import Polynomial.Simple.Solver
--
-- * Is that all?
--       No! As it happens, even the simple solver is complicated to use.
--       You'll *actually* want to use the reflection-based interface:
import Polynomial.Simple.Reflection
--
-- * And what about the step-by-step stuff?
--       That all uses the same underlying solver as the other stuff, with a
--       special *relation*. You can check that out here:
import Relation.Traced
