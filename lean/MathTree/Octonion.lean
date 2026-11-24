module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic

/-!
# Octonions (Cayley–Dickson doubling of the quaternions)

Mathlib has no octonions. This file gives the carrier and the product as a specification;
the algebra structure and Hurwitz's theorem are left for later.
-/

@[expose] public section

/-- An octonion as a pair of real quaternions (Cayley–Dickson construction). -/
structure Octonion where
  /-- first quaternion -/
  a : Quaternion ℝ
  /-- second quaternion -/
  b : Quaternion ℝ

namespace Octonion

/-- Cayley–Dickson product `(a, b) * (c, d) = (a c − d* b, d a + b c*)`. -/
def mul (x y : Octonion) : Octonion :=
  ⟨x.a * y.a - star y.b * x.b, y.b * x.a + x.b * star y.a⟩

instance : Mul Octonion := ⟨mul⟩

/-- Componentwise addition. -/
instance : Add Octonion := ⟨fun x y => ⟨x.a + y.a, x.b + y.b⟩⟩

end Octonion
