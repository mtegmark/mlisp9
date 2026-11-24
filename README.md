# mathtree

Code for the paper on the family tree of mathematical structures and its website
<https://tegmark.org/mathtree>: the Lean 4 library, the implementations of the two minimal LISPs
**MLISP** (nine symbols) and **mLISP** (seven symbols) in Python, C, JavaScript and Lean.

## Contents

| Path | What it is |
|---|---|
| `lean/` | The Lean 4 project: the subset of Mathlib that the boxes of the tree use, and the MathTree library on top, including the formalization of MLISP and mLISP |
| `mlisp9/` | MLISP, the nine-symbol language `a b c d f 0 i j k`: `python/mlisp.py` (reference interpreter), `python/library/` (the programs for the countable structures with their self-test), `c/mlisp.c`, `js/` (the engine of the calculator page) |
| `mlisp7/` | mLISP, the seven-symbol language `0 a b c d e f`: `python/mlisp7.py`, `c/mlisp7.c`, `js/` (engine and 118 test cases) |

## The two languages

Values are binary trees over one atom: `0` is the atom and `c` pairs two values, so a value is
written as a postfix string over `0` and `c` (`0000ccc` is the natural number 3). A program is a
postfix string of one-character symbols: `a` first part, `b` second part, `c` pair, `d` decide
(lazy), `f` recursion and `0` the atom, plus symbols defined by writing `X<program>#` before the
program. In MLISP a function has up to three arguments `i j k`. In mLISP every function takes one
argument `e`, and `i j k` are accessor macros for the parts of a pair or triple. The docstrings of
`mlisp9/python/mlisp.py` and `mlisp7/python/mlisp7.py` are the full descriptions. Interactive
calculators: <https://tegmark.org/mathtree/mlisp.html> and
<https://tegmark.org/mathtree/mlisp7.html>.

```
python3 mlisp9/python/mlisp.py -t 'ij+' 0000ccc 00000cccc       # 3 + 4 -> 00000000ccccccc
python3 mlisp7/python/mlisp7.py -t 'ijc+' 0000ccc 00000cccc     # the same in mLISP
(cd mlisp9/python/library && python3 programs.py)                # self-test, prints the programs
cc -O2 -o mlisp mlisp9/c/mlisp.c && ./mlisp 'ijc' 0 00c
cc -O2 -o mlisp7 mlisp7/c/mlisp7.c && ./mlisp7 'ijc' 0 00c
(cd mlisp7/js && node test_mlisp7.js)
```

## Lean (`lean/`)

A self-contained Lake project (toolchain `v4.35.0-rc3`): the subset of Mathlib that the boxes of
the tree use, closed under imports (`lean/Mathlib/`, copied unchanged from Mathlib commit
`a79b0d2`), and the MathTree library on top. See `lean/README.md` for its layout.

| File | Content |
|---|---|
| `MathTree/MLISP.lean` | MLISP: values, parser, lazy big-step semantics (deterministic), evaluator (sound), the table programs proved correct (arithmetic, primality, integers, rationals, equality, the meta-circular evaluator) |
| `MathTree/MLISPTuring.lean` | Turing completeness of MLISP |
| `MathTree/Clones.lean` | Presentations, mathematical structures as isomorphism classes, clones (compositional closure) and their equality with Mathlib's term functions; the examples of mutual generation |
| `MathTree/DoubleField.lean`, `TripleField.lean`, `QuadrupleField.lean`, `Octonion.lean`, `Arithmetic.lean` | Theories of the tree that Mathlib lacks |
| `MathTree.lean` | One import block per box of the tree |
| `KEY_THEOREMS.md` | The key theorems of every box with the Lean declaration that proves each |

mLISP is the fragment of MLISP in which every function has at most one argument, with the
argument symbol spelled `e`. Under the embedding `e -> i` every mLISP program is an MLISP program
with the same meaning, so `MLISP.lean` and `MLISPTuring.lean` formalize both languages.

```
cd lean
lake build MathTree
```

A build from a fresh clone compiles the Mathlib subset from source (hours on a laptop); the
library was last built successfully from the working copy this repository was made from.

## License

Apache 2.0 (see `LICENSE`). The files under `lean/Mathlib/` and `lean/scripts/` are Mathlib's,
Copyright the Mathlib contributors.
