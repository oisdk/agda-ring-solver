module Positional.Binary where

open import Data.List as List using (List; []; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc)

-- A list of zero runs.
--
-- 0  = []
-- 52 = 001011 = [2,1,0]
-- 4  = 001    = [2]
Bin : Set
Bin = List ℕ
