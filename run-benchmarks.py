preamble = """module Benchmarks where
open import Data.Nat using (ℕ)

"""

sparse_preamble = """
open import Polynomial.Simple.AlmostCommutativeRing
open import Polynomial.Simple.Reflection
open import Data.Nat using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Level using (0ℓ)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (refl)

NatRing : AlmostCommutativeRing 0ℓ 0ℓ
NatRing = fromCommutativeSemiring *-+-commutativeSemiring λ { zero → just refl ; (suc x) → nothing}

open AlmostCommutativeRing NatRing
"""

dense_preamble = """
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver
"""

expressions = [
    ("(v + w + x + y + z) ^ d", list(range(1,9))),
    ("v ^ d + w ^ d + x ^ d + y ^ d + z ^ d",[1,100,200,300,400,500]),
    ("(k 1 + v ^ 1 + w ^ 2 + x ^ 3 + y ^ 4 + z ^ 5) ^ d",list(range(1,9)))
]

dense_expr_encoding = str.maketrans({'+' : ':+', '^' : ':^', '*' : ':*', 'k' : 'con'})
sparse_expr_encoding = str.maketrans({'k': ''})

import subprocess
import os
import time

def line_by_line(command):
    return subprocess.check_output(command, universal_newlines=True).split('\n')

for expr_, degrees in expressions:
    header = expr_.translate(sparse_expr_encoding)
    print(header)
    print('%-3s | %-7s | %-7s |' % ('d', 'sparse', 'dense'))
    for degree in degrees:
        print((('%3i | ' % degree)), end='')
        expr = expr_.replace('d', str(degree))
        pretty_expr = expr.translate(sparse_expr_encoding)
        try:
            os.remove('src/Benchmarks.agdai')
        except:
            pass
        try:
            with open('src/Benchmarks.agda', 'w') as benchfile:
                benchfile.write(preamble)
                benchfile.write(sparse_preamble)
                benchfile.write('lemma : ' + "∀ v w x y z → " + pretty_expr + " ≈ " + pretty_expr + '\n')
                benchfile.write('lemma = solve NatRing')
            before = time.time()
            subprocess.run(['agda', '--no-syntactic-equality', 'src/Benchmarks.agda'], capture_output=True, check=True)
            after = time.time()
            print(('%7g | ' % (after-before)), end='')
        finally:
            os.remove('src/Benchmarks.agda')
        try:
            os.remove('src/Benchmarks.agdai')
        except:
            pass
        try:
            with open('src/Benchmarks.agda', 'w') as benchfile:
                benchfile.write(preamble)
                benchfile.write(dense_preamble)
                benchfile.write('lemma : ' + "∀ v w x y z → " + pretty_expr + " ≡ " + pretty_expr + '\n')
                benchfile.write('lemma = solve 5 (λ v w x y z → ' + expr.translate(dense_expr_encoding) + " := " + expr.translate(dense_expr_encoding) + ") refl")
            before = time.time()
            subprocess.run(['agda', '--no-syntactic-equality', 'src/Benchmarks.agda'], capture_output=True, check=True)
            after = time.time()
            print(('%7g | ' % (after-before)))
        finally:
            os.remove('src/Benchmarks.agda')
