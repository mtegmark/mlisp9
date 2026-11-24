module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Basic

/-!
# Double fields

A double field, in the sense of the math tree: a field `D` (the outer field, written with the
standard names `0`, `1`, `+`, `*`) whose nonzero elements carry a second field structure (the inner
field) in which addition is the outer multiplication. The atlas writes the outer zero as `∞` and
the outer unit as `0`; here the outer field keeps Lean's names and the inner field lives on the
subtype of nonzero elements. Not part of Mathlib.
-/

@[expose] public section

/-- A double field structure on a field `D`: an inner field on `{x : D // x ≠ 0}` whose addition
is the outer multiplication. -/
structure DoubleField (D : Type*) [Field D] where
  /-- the inner field, on the nonzero elements -/
  inner : Field {x : D // x ≠ 0}
  /-- inner addition is outer multiplication -/
  compat : ∀ a b : {x : D // x ≠ 0},
    ((@HAdd.hAdd _ _ _ (@instHAdd _ inner.toAdd) a b : {x : D // x ≠ 0}) : D) = (a : D) * b

namespace DoubleField

variable {D : Type*} [Field D] (S : DoubleField D)

/-- The inner zero is the outer one: it is the identity of the inner addition, hence of the outer
multiplication on nonzero elements. -/
theorem inner_zero_val :
    ((@OfNat.ofNat _ 0 (@Zero.toOfNat0 _ S.inner.toZero) : {x : D // x ≠ 0}) : D) = 1 := by
  let _ := S.inner
  have h := S.compat 0 0
  have hzz : (@HAdd.hAdd _ _ _ (@instHAdd _ S.inner.toAdd) (0 : {x : D // x ≠ 0}) 0) = 0 := add_zero 0
  rw [hzz] at h
  exact (mul_eq_left₀ (Subtype.prop (0 : {x : D // x ≠ 0}))).mp h.symm

end DoubleField
