module

public import MathTree.TripleField
public import Batteries.Util.ProofWanted

/-!
# Quadruple fields

A quadruple field is a double field whose inner field carries a triple field: four nested field
structures, each multiplication being the next addition. None exists: the inner three fields form the
unique triple field, which has four elements, so the outer field is `GF(5)`, whose multiplicative group
`C₄` is cyclic, while the additive group of the four-element middle field is `C₂ × C₂`. The statement
`QuadrupleField.isEmpty` records this and is left as a `proof_wanted`.
-/

@[expose] public section

/-- A quadruple field on a field `Q`: a double field whose inner field carries a triple field. -/
structure QuadrupleField (Q : Type*) [Field Q] where
  /-- the double field structure on `Q` -/
  outer : DoubleField Q
  /-- a triple field structure on the inner field of `outer` -/
  inner : @TripleField {x : Q // x ≠ 0} outer.inner

/-- No finite field carries a quadruple field structure. -/
proof_wanted QuadrupleField.isEmpty (Q : Type*) [Field Q] [Finite Q] : IsEmpty (QuadrupleField Q)
