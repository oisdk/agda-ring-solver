library_file = """
name: agda-algebra-benchmarks
depend: standard-library, agda-algebra
include: src
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
open import Agda.Builtin.FromNat
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver

import Data.Nat.Literals
open import Data.Unit using (⊤)

instance
  natLit : Number ℕ
  natLit = Data.Nat.Literals.number

instance
  exprLit : ∀ {n} → Number (Polynomial n)
  exprLit = record
    { Constraint = λ _ → ⊤
    ; fromNat = λ x → con x
    }
"""


def expr_1(n):
    return '(' + ' + '.join('x%i' % i for i in range(1, n + 1)) + ') ^ d'


def expr_2(n):
    return ' + '.join('x%i ^ d' % i for i in range(1, n + 1))


def expr_3(n):
    return '(1 + ' + ' + '.join('x%i ^ %i' % (i , i) for i in range(1, n + 1)) + ') ^ d'


expressions = [
    (expr_1, list(range(1, 9))),
    (expr_2, [1, 100, 200, 300, 400, 500]),
    (expr_3, list(range(1, 9))),
]

import sympy


def expand(expr):
    return str(sympy.sympify(expr.replace('^', '**')).expand()).replace(
        '**', ' ^ ').replace('*', ' * ')


dense_expr_encoding = str.maketrans({'+': ':+', '^': ':^', '*': ':*'})

import subprocess
import os
import time
import sys
import tempfile
import datetime


class cd:
    def __init__(self, newPath):
        self.newPath = os.path.expanduser(newPath)

    def __enter__(self):
        self.savedPath = os.getcwd()
        os.chdir(self.newPath)

    def __exit__(self, etype, value, traceback):
        os.chdir(self.savedPath)


def time_file_typecheck(contents):
    with tempfile.TemporaryDirectory() as benchdir, cd(benchdir):
        with open('agda-algebra-benchmarks.agda-lib', 'w') as libfile:
            libfile.write(library_file)
        os.mkdir('src')
        with open('src/Benchmarks.agda', 'w') as benchfile:
            benchfile.write('module Benchmarks where\n')
            benchfile.write(contents)
        before = time.time()
        subprocess.run(
            ['agda', 'src/Benchmarks.agda'], capture_output=True, check=True)
        return time.time() - before


def print_graph(degrees, sparse_results, dense_results):
    width = 9 + len(degrees) * 10
    print('-' * width)
    max_res = max(sparse_results + dense_results)
    sparse_ys = [int((y * 40) / max_res) for y in sparse_results]
    dense_ys = [int((y * 40) / max_res) for y in dense_results]
    for y in range(39, -1, -1):
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
    for x in range(1, len(degrees)+1):
        deg = (x * max_deg) / (len(degrees))
        print('%-10i' % round(deg), end='')
    print()

for n in range(5, 9):
    varnames = ' '.join('x' + str(i) for i in range(1, n + 1))
    for expr_fn, degrees in expressions:
        expr_ = expr_fn(n)
        print(expr_)
        print('%3s | %-7s | %-7s |' % ('d', 'sparse', 'dense'))
        sparse_results = []
        dense_results = []
        for degree in degrees:
            print((('%3i | ' % degree)), end='')
            sys.stdout.flush()
            expr = expr_.replace('d', str(degree))
            typesig = 'lemma : ∀ %s → %s ≈ %s' % (varnames, expr, expand(expr))
            res = time_file_typecheck('\n'.join((sparse_preamble, typesig,
                                                 'lemma = solve NatRing')))
            print(('%7g | ' % res), end='')
            sys.stdout.flush()
            sparse_results.append(res)
            typesig = 'lemma : ∀ %s → %s ≡ %s' % (varnames, expr, expand(expr))
            expr_ast = 'lemma = solve %i (λ %s → %s := %s ) refl' % (
                n, varnames, expr.translate(dense_expr_encoding),
                expand(expr).translate(dense_expr_encoding))
            res = time_file_typecheck('\n'.join((dense_preamble, typesig,
                                                 expr_ast)))
            print(('%7g | ' % res))
            sys.stdout.flush()
            dense_results.append(res)
        print()
        print_graph(degrees, sparse_results, dense_results)
        print()
        with open('benchmark-logs', 'a') as logfile:
            logfile.write(str(datetime.datetime.now()) + '\n')
            logfile.write(expr_ + '\n')
            logfile.write('d sparse dense\n')
            for d, sp, dn in zip(degrees, sparse_results, dense_results):
                logfile.write(d.__repr__() + ' ' + sp.__repr__() + ' ' + dn.__repr__() + '\n')
            logfile.write('\n\n')
