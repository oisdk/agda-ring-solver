-- 2011-07-13 example by Uli Schoepp in the role of an Agda-newbie
module Issue426 where

data Bool : Set where
  false : Bool
  true : Bool

if : forall {A : Set} -> Bool -> A -> A -> A
if true x y = x
if false x y = y

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN SUC succ #-}
{-# BUILTIN ZERO zero #-}

leq : Nat -> Nat -> Bool
leq 0 m = true
leq (succ n) 0 = false
leq (succ n) (succ m) = leq n m

mod : Nat -> Nat -> Nat
mod 0 k = 0
mod (succ n) k = if (leq (succ r) k) r 0
  where r = succ (mod n k)

test = mod 25 4 
-- C-c C-n test
-- takes very long, due to call-by-name evaluation strategy
-- would not want to try  mod 30 4  
