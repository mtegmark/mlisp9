module

public import MathTree.DoubleField
public import Mathlib.Basic.Finite.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Batteries.Util.ProofWanted

/-!
# Triple fields

A triple field is a double field whose inner field is itself the outer field of a double field.
Exactly one finite triple field exists, on four elements: `GF(4) ⊃ GF(3) ⊃ GF(2)` (the counting
argument of the atlas leaves only this case, and it exists by transport of structure). The statement
`TripleField.card_eq_four` records the size bound and is left as a `proof_wanted`, which elaborates
without a `sorry`; nothing about triple fields is proved here. An earlier version of this file stated
the nonexistence of triple fields, which is false.
-/

@[expose] public section

/-- A triple field on a field `T`: a double field whose inner field carries a double field. -/
structure TripleField (T : Type*) [Field T] where
  /-- the double field structure on `T` -/
  middle : DoubleField T
  /-- a double field structure on the inner field of `middle` -/
  inner : @DoubleField {x : T // x ≠ 0} middle.inner

/-- Every finite triple field has exactly four elements (the atlas's counting argument). -/
proof_wanted TripleField.card_eq_four (T : Type*) [Field T] [Finite T] (h : TripleField T) :
    Nat.card T = 4
