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
--                                            21 January 2019

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
--     https://github.com/oisdk/agda-algebra-report
--
-- ███████╗██╗  ██╗ █████╗ ███╗   ███╗██████╗ ██╗     ███████╗███████╗
-- ██╔════╝╚██╗██╔╝██╔══██╗████╗ ████║██╔══██╗██║     ██╔════╝██╔════╝
-- █████╗   ╚███╔╝ ███████║██╔████╔██║██████╔╝██║     █████╗  ███████╗ ████████████████████╗
-- ██╔══╝   ██╔██╗ ██╔══██║██║╚██╔╝██║██╔═══╝ ██║     ██╔══╝  ╚════██║ ╚═════════════════██║
-- ███████╗██╔╝ ██╗██║  ██║██║ ╚═╝ ██║██║     ███████╗███████╗███████║                   ██║
-- ╚══════╝╚═╝  ╚═╝╚═╝  ╚═╝╚═╝     ╚═╝╚═╝     ╚══════╝╚══════╝╚══════╝                   ██║
--                                                                                       ██║
--------------------------------------------------------------------------------         ██║
-- You can ignore this bit! We're just overloading the literals Agda uses for --         ██║
-- numbers This bit isn't necessary if you're just using ℕ, or if you         --         ██║
-- construct your type directly. We only really do it here so that we can use --         ██║
-- different numeric types in the same file.                                  --         ██║
                                                                              --         ██║
open import Agda.Builtin.FromNat                                              --         ██║
open import Data.Nat as ℕ using (ℕ)                                           --         ██║
open import Data.Integer as ℤ using (ℤ)                                       --         ██║
                                                                              --         ██║
instance                                                                      --         ██║
  numberNat : Number ℕ                                                        --         ██║
  numberNat = Data.Nat.Literals.number                                        --         ██║
    where import Data.Nat.Literals                                            --         ██║
                                                                              --         ██║
instance                                                                      --         ██║
  numberInt : Number ℤ                                                        --         ██║
  numberInt = Data.Integer.Literals.number                                    --         ██║
    where import Data.Integer.Literals                                        --         ██║
                                                                              --         ██║
--------------------------------------------------------------------------------         ██║
-- Imports!                                                                   --         ██║
                                                                              --         ██║
open import Polynomial.Simple.AlmostCommutativeRing                           --         ██║
open import Polynomial.Simple.AlmostCommutativeRing.Instances                 --         ██║
open import Polynomial.Simple.Reflection                                      --         ██║
--------------------------------------------------------------------------------         ██║
--                                                                            --         ██║
--                           8888888888',8888'                                --         ██║
--                                  ,8',8888'                                 --         ██║
--                                 ,8',8888'                                  --         ██║
--                                ,8',8888'                                   --         ██║
--                               ,8',8888'                                    --         ██║
--                              ,8',8888'                                     --         ██║
--                             ,8',8888'                                      --         ██║
--                            ,8',8888'                                       --         ██║
--                           ,8',8888'                                        --         ██║
--                          ,8',8888888888888                                 --         ██║
--                                                                            --         ██║
--------------------------------------------------------------------------------         ██║
--                                                                            --         ██║
module IntExamples where                                                      --         ██║
  open AlmostCommutativeRing Int.ring                                         --         ██║
  -- Everything is automatic: you just ask Agda to solve it and it does!      --     ██╗ ██║
  lemma₁ : ∀ x y → x + y * 1 + 3 ≈ 3 + 1 + y + x + - 1                        --   ████║ ██║
  lemma₁ = solve Int.ring                                                     -- ██████████║
                                                                              --   ████╔═██║
  lemma₂ : ∀ x y → (x + y) ^ 2 ≈ x ^ 2 + 2 * x * y + y ^ 2                    --     ██║ ██║
  lemma₂ = solve Int.ring                                                     --     ╚═╝ ██║
--                                                                            --         ██║
--------------------------------------------------------------------------------         ██║
--                                                                            --         ██║
--                          b.             8                                  --         ██║
--                          888o.          8                                  --         ██║
--                          Y88888o.       8                                  --         ██║
--                          .`Y888888o.    8                                  --         ██║
--                          8o. `Y888888o. 8                                  --         ██║
--                          8`Y8o. `Y88888o8                                  --         ██║
--                          8   `Y8o. `Y8888                                  --         ██║
--                          8      `Y8o. `Y8                                  --         ██║
--                          8         `Y8o.`                                  --         ██║
--                          8            `Yo                                  --         ██║
--                                                                            --         ██║
--------------------------------------------------------------------------------         ██║
--                                                                            --         ██║
module NatExamples where                                                      --         ██║
  open AlmostCommutativeRing Nat.ring                                         --         ██║
  -- The solver is flexible enoough to work with ℕ (even though it asks for   --     ██╗ ██║
  -- rings!)                                                                  --   ████║ ██║
  lemma : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x                               -- ██████████║
  lemma = solve Nat.ring                                                      --   ████╔═██║
                                                                              --     ██║ ██║
--------------------------------------------------------------------------------     ╚═╝ ██║
--                                                                            --         ██║
--          d888888o.   8888888 8888888888 8 8888888888   8 888888888o        --         ██║
--        .`8888:' `88.       8 8888       8 8888         8 8888    `88.      --         ██║
--        8.`8888.   Y8       8 8888       8 8888         8 8888     `88      --         ██║
--        `8.`8888.           8 8888       8 8888         8 8888     ,88      --         ██║
--         `8.`8888.          8 8888       8 888888888888 8 8888.   ,88'      --         ██║
--          `8.`8888.         8 8888       8 8888         8 888888888P'       --         ██║
--           `8.`8888.        8 8888       8 8888         8 8888              --         ██║
--       8b   `8.`8888.       8 8888       8 8888         8 8888              --         ██║
--       `8b.  ;8.`8888       8 8888       8 8888         8 8888              --         ██║
--        `Y8888P ,88P'       8 8888       8 888888888888 8 8888              --         ██║
--                                                                            --         ██║
--                      8 888888888o   `8.`8888.      ,8'                     --         ██║
--                      8 8888    `88.  `8.`8888.    ,8'                      --         ██║
--                      8 8888     `88   `8.`8888.  ,8'                       --         ██║
--                      8 8888     ,88    `8.`8888.,8'                        --         ██║
--                      8 8888.   ,88'     `8.`88888'                         --         ██║
--                      8 8888888888        `8. 8888                          --         ██║
--                      8 8888    `88.       `8 8888                          --         ██║
--                      8 8888      88        8 8888                          --         ██║
--                      8 8888    ,88'        8 8888                          --         ██║
--                      8 888888888P          8 8888                          --         ██║
--                                                                            --         ██║
--          d888888o.   8888888 8888888888 8 8888888888   8 888888888o        --         ██║
--        .`8888:' `88.       8 8888       8 8888         8 8888    `88.      --         ██║
--        8.`8888.   Y8       8 8888       8 8888         8 8888     `88      --         ██║
--        `8.`8888.           8 8888       8 8888         8 8888     ,88      --         ██║
--         `8.`8888.          8 8888       8 888888888888 8 8888.   ,88'      --         ██║
--          `8.`8888.         8 8888       8 8888         8 888888888P'       --         ██║
--           `8.`8888.        8 8888       8 8888         8 8888              --         ██║
--       8b   `8.`8888.       8 8888       8 8888         8 8888              --         ██║
--       `8b.  ;8.`8888       8 8888       8 8888         8 8888              --         ██║
--        `Y8888P ,88P'       8 8888       8 888888888888 8 8888              --         ██║
--                                                                            --         ██║
--------------------------------------------------------------------------------         ██║
-- Don't understand why something works? Wanna get it explained to you? Now   --         ██║
-- you can! The solver can generate step-by-step, human-readable solutions    --         ██║
-- for learning purposes.                                                     --         ██║
--                                                                            --         ██║
module TracedExamples where                                                   --         ██║
  import Data.Nat.Show                                                        --         ██║
  open import Data.List using (_∷_; [])                                       --         ██║
  open import Agda.Builtin.Nat using (_==_)                                   --         ██║
  open import Relation.Traced Nat.ring _==_ Data.Nat.Show.show public         --         ██║
  open AlmostCommutativeRing tracedRing                                       --         ██║
  open import Relation.Binary.PropositionalEquality as ≡ using (_≡_)          --         ██║
                                                                              --         ██║
  lemma : ∀ x y → x + y * 1 + 3 ≈ 2 + 1 + y + x                               --         ██║
  lemma = solve tracedRing                                                    --         ██║
                                                                              --      ██╗██║
  explained                                                                   --    ████║██║
    : showProof (lemma "x" "y") ≡ "x + (y + 3)"                               --  █████████║
                                ∷ "    ={ +-comm(x, y + 3) }"                 --    ████╔══╝
                                ∷ "y + 3 + x"                                 --      ██║
                                ∷ "    ={ +-comm(y, 3) }"                     --      ╚═╝
                                ∷ "3 + y + x"                                 --
                                ∷ []                                          --
  explained = ≡.refl                                                          --
--------------------------------------------------------------------------------
-- 510 |                                                                        
-- 495 |                                                                       *
-- 480 |                                                                        
-- 465 |                                                                        
-- 450 |                                                                        
-- 435 |                                                                        
-- 420 |                                                                        
-- 405 |                                                                        
-- 390 |                                                                        
-- 375 |                                                                        
-- 360 |                                                                        
-- 345 |                                                                        
-- 330 |                                                                        
-- 315 |                                                                        
-- 300 |                                                                        
-- 285 |                                                                        
-- 270 |                                                                        
-- 255 |                                                                        
-- 240 |                                                                        
-- 225 |                                                                        
-- 210 |                                                                        
-- 195 |                                                                        
-- 180 |                                                                        
-- 165 |                                                                        
-- 150 |                                                                        
-- 135 |                                                                        
-- 120 |                                                                        
-- 105 |                                                             *          
--  90 |                                                                        
--  75 |                                                                        
--  60 |                                                                       +
--  45 |                                                                        
--  30 |                                                                        
--  15 |                                                   *         +          
--   0 | *         *         *         *         *         +                    
--     --------------------------------------------------------------------------
--       1         2         3         4         5         6         7         8

-- -- The solver uses an internal representation of Horner Normal Form:
-- -- information on it is available in:
-- import Polynomial.NormalForm

-- -- The homomorphism proofs are in:
-- import Polynomial.Homomorphism

-- -- The "full" solver (which allows for different types of coefficients
-- -- and carriers) is available in
-- import Polynomial.Solver

-- -- However, the more commonly-used solver is in:
-- import Polynomial.Simple.Solver

-- -- The implementation of the reflection machinery is in:
-- import Polynomial.Simple.Reflection
