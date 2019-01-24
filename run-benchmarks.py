library_file = """
name: agda-ring-solver-benchmarks
depend: standard-library, agda-ring-solver
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
    return '(1 + ' + ' + '.join('x%i ^ %i' % (i, i)
                                for i in range(1, n + 1)) + ') ^ d'

def expr_4(n):
    return '(' + ' + '.join('x%i ^ %i' % (i, (n+1) - i)
                                for i in range(1, n + 1)) + ' + 1) ^ d'

expressions = [
    (expr_1, '(x1 + x2 + ... + xn) ^ d'),
    (expr_2, 'x1 ^ d + x2 ^ d + ... + xn ^ d'),
    (expr_3, '(1 + x1 ^ 1 + x2 ^ 2 + ... + xn ^ n) ^ d'),
    (expr_4, '(x1 ^ n + x2 ^ (n-1) + ... + xn ^ 1 + 1) ^ d'),
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
        with open('agda-ring-solver-benchmarks.agda-lib', 'w') as libfile:
            libfile.write(library_file)
        os.mkdir('src')
        with open('src/Benchmarks.agda', 'w') as benchfile:
            benchfile.write('module Benchmarks where\n')
            benchfile.write(contents)
        before = time.time()
        try:
            proc = subprocess.run(
                ['agda', 'src/Benchmarks.agda'],
                capture_output=True,
                text=True)
            res = time.time() - before
            proc.check_returncode()
            return res
        except subprocess.CalledProcessError as err:
            print('\n' + proc.stdout)
            raise err

import itertools
import math

def print_graph(degrees, sparse_results, dense_results):
    sparse_data = '\n'.join('%i %g' % (d, r) for (d, r) in zip(degrees, sparse_results))
    dense_data  = '\n'.join('%i %g' % (d, r) for (d, r) in zip(degrees, dense_results))
    xpadding = math.ceil(max(degrees) / 10)
    ypadding = math.ceil(max(sparse_results + dense_results) / 10)
    ymin = int(min(sparse_results + dense_results)) - ypadding
    ymax = math.ceil(max(sparse_results + dense_results)) + ypadding
    data_file = """
$sparse << EOD
%s
EOD
$dense << EOD
%s
EOD
set terminal dumb size 80,40 ansi256
set xrange [%i:%i]
set yrange [%i:%i]
plot $sparse title "sparse", $dense title "dense"
undefine $*
""" % (sparse_data, dense_data, min(degrees) - xpadding, max(degrees) + xpadding, ymin, ymax)
    subprocess.run(['gnuplot'], input=data_file, text=True)

print('Choose an expression: ')
for i, (_, expr_desc) in enumerate(expressions):
    print('%2i : %s' % (i, expr_desc))
expr_fn = expressions[int(input('> '))][0]
n = int(input('Choose n:\n> '))
degrees = [ int(d) for d in input('Choose degrees (default= 1 2 3 4 5 6 7 8)\n> ').split() ] or list(range(1,9))
benchopts = [['sparse'], ['dense'], ['sparse', 'dense']]
for i, opts in enumerate(benchopts):
    print('%2i : %s' % (i, ' & '.join(opts)))
benches = benchopts[int(input('Choose things to benchmark\n> '))]
varnames = ' '.join('x' + str(i) for i in range(1, n + 1))
expr_ = expr_fn(n)
print(expr_)
print('%3s | %-7s | %-7s |' % ('d', 'sparse', 'dense'))
sparse_results = []
dense_results = []
for degree in degrees:
    print((('%3i | ' % degree)), end='')
    sys.stdout.flush()
    expr = expr_.replace('d', str(degree))
    if 'sparse' in benches:
        typesig = 'lemma : ∀ %s → %s ≈ %s' % (varnames, expr, expand(expr))
        res = time_file_typecheck('\n'.join((sparse_preamble, typesig,
                                                'lemma = solve NatRing')))
        print(('%7g | ' % res), end='')
        sparse_results.append(res)
    else:
        print('...     | ', end='')
    sys.stdout.flush()
    if 'dense' in benches:
        typesig = 'lemma : ∀ %s → %s ≡ %s' % (varnames, expr, expand(expr))
        expr_ast = 'lemma = solve %i (λ %s → %s := %s ) refl' % (
            n, varnames, expr.translate(dense_expr_encoding),
            expand(expr).translate(dense_expr_encoding))
        res = time_file_typecheck('\n'.join((dense_preamble, typesig,
                                            expr_ast)))
        print(('%7g | ' % res))
        dense_results.append(res)
    else:
        print('...     | ')
    sys.stdout.flush()
print()
print_graph(degrees, sparse_results, dense_results)
print()
with open('benchmark-logs', 'a') as logfile:
    logfile.write(str(datetime.datetime.now()) + '\n')
    logfile.write(expr_ + '\n')
    logfile.write('d sparse dense\n')
    for d, sp, dn in itertools.zip_longest(degrees, sparse_results, dense_results):
        logfile.write(d.__repr__() + ' ' + sp.__repr__() + ' ' +
                        dn.__repr__() + '\n')
    logfile.write('\n\n')
