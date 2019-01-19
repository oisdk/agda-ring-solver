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
    ("v ^ d + w ^ d + x ^ d + y ^ d + z ^ d",[1,100,200,300,400,500]),
    ("(k1 + v ^ 1 + w ^ 2 + x ^ 3 + y ^ 4 + z ^ 5) ^ d",list(range(1,9))),
    ("(v + w + x + y + z) ^ d", list(range(1,9))),
]

dense_expr_encoding = str.maketrans({'+' : ':+', '^' : ':^', '*' : ':*', 'k' : 'con '})
sparse_expr_encoding = str.maketrans({'k': ''})

import subprocess
import os
import time
import sys

def line_by_line(command):
    return subprocess.check_output(command, universal_newlines=True).split('\n')

for expr_, degrees in expressions:
    header = expr_.translate(sparse_expr_encoding)
    print(header)
    print('%3s | %-7s | %-7s |' % ('d', 'sparse', 'dense'))
    sparse_results = []
    dense_results = []
    for degree in degrees:
        print((('%3i | ' % degree)), end='')
        sys.stdout.flush()
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
            res = after-before
            print(('%7g | ' % res), end='')
            sys.stdout.flush()
            sparse_results.append(res)
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
            res = after-before
            print(('%7g | ' % res))
            sys.stdout.flush()
            dense_results.append(res)
        finally:
            os.remove('src/Benchmarks.agda')
    print()

    width = 9 + len(degrees) * 10
    print('-' * width)
    max_res = max(sparse_results+dense_results)
    sparse_ys = [ int((y * 39) / max_res) for y in sparse_results ]
    dense_ys  = [ int((y * 39) / max_res) for y in dense_results ]
    for y in reversed(range(40)):
        print('%5i | ' % int((y / 40) * max_res), end='')
        for y_s, y_d in zip(sparse_ys, dense_ys):
            if y == y_d:
                print('*' + ' ' * 9, end='')
            elif y == y_s:
                print('+' + ' ' * 9, end='')
            else:
                print(' ' * 10, end='')
        print('|')
    max_deg = max(degrees)
    print('-' * width)
    print(' ' * 4, end='d = ')
    for x in range(len(degrees)):
        print(('%-10i' % round((x / (len(degrees))) * max_deg)), end='')
    print()
    print()
