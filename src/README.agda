module README where

-- Donnacha Oisín Kidney

-- This contains the worked-through source code for "A fast and Efficient
-- Polynomial Solver in Agda".

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
