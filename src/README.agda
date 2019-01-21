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

-- To jump straight into some examples, look in:
import Examples

-- The solver uses an internal representation of Horner Normal Form:
-- information on it is available in:
import Polynomial.NormalForm

-- The homomorphism proofs are in:
import Polynomial.Homomorphism

-- The "full" solver (which allows for different types of coefficients
-- and carriers) is available in
import Polynomial.Solver

-- However, the more commonly-used solver is in:
import Polynomial.Simple.Solver

-- The implementation of the reflection machinery is in:
import Polynomial.Simple.Reflection
