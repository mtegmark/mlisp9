# MathTreeMathlib

The subset of Mathlib corresponding to the boxes of the math tree (<https://tegmark.org/mathtree>), closed under imports, with the MathTree library on top. Generated from Mathlib commit `a79b0d2` (toolchain `leanprover/lean4:v4.35.0-rc3`).

- Boxes: 54, of which 49 have Mathlib modules and 5 (`df, tf, rq, pa, oo`) are defined in `MathTree/`.
- Root modules named in `mathtree_modules.json`: 119. Import closure inside Mathlib: 3468 of 8554 modules (40.5%).
- External packages imported by the closure: Aesop, Batteries, ImportGraph, Init, Lean, LeanSearchClient, Plausible, ProofWidgets, Qq, Std, statements (all of Mathlib's dependencies are kept in the lakefile so that the pinned manifest can be reused).
- Modules per top-level Mathlib directory: Algebra 703, Data 383, Topology 325, Analysis 294, Tactic 263, RingTheory 236, CategoryTheory 209, Order 204, LinearAlgebra 160, MeasureTheory 158, GroupTheory 73, Basic 41, FieldTheory 38, Logic 37, SetTheory 32, Geometry 29, Lean 26, Util 24, Combinatorics 22, ModelTheory 14, Control 9, NumberTheory 8, Dynamics 7, Probability 2, Computability 1, Init 1

## Layout

- `Mathlib/`: the copied modules, unchanged. `Mathlib.lean` imports all of them.
- `MathTree.lean`: one import block per box, in tree order.
- `MathTree/DoubleField.lean`, `TripleField.lean`, `Octonion.lean`, `Arithmetic.lean`: structures the tree has and Mathlib lacks.
- `MathTree/MLISP.lean`, `MLISPTuring.lean`: the formalization of MLISP. `MathTree/Clones.lean`: presentations, structures and clones.

## Build

```
cd lean
lake build MathTree
```

## License and attribution

The files under `Mathlib/` and `scripts/` are copied unchanged from
[Mathlib](https://github.com/leanprover-community/mathlib4), Copyright the Mathlib contributors,
released under the Apache 2.0 license (see `LICENSE`, which is Mathlib's). The files under
`MathTree/`, and the root modules are released under the same license.

## Building from a fresh clone

`lake build` compiles the 3468 Mathlib modules from source, which takes a few hours on a laptop
(Mathlib's `lake exe cache get` does not serve this repackaged subset). The dependency packages are
fetched automatically from the pinned revisions in `lake-manifest.json`. Requires
[elan](https://github.com/leanprover/elan); the toolchain in `lean-toolchain` is installed on demand.

```
git clone https://github.com/metegmark/mathtree.git
cd mathtree/lean
lake build MathTree
```
