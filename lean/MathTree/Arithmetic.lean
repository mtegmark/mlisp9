module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Int.Basic

/-!
# Robinson and Presburger arithmetic

Mathlib has neither theory as an object; Lean's `ℕ` is their standard model, with the axioms as
theorems, and the `omega` tactic is a decision procedure for (quantifier-free) Presburger
arithmetic. This file records the seven axioms of Robinson arithmetic as theorems about `ℕ` and
one Presburger example decided by `omega`.
-/

@[expose] public section

namespace RobinsonArithmetic

theorem ax1 (a : ℕ) : a + 1 ≠ 0 := Nat.succ_ne_zero a
theorem ax2 (a b : ℕ) : a + 1 = b + 1 → a = b := Nat.succ.inj
theorem ax3 (a : ℕ) : a ≠ 0 → ∃ b, a = b + 1 := Nat.exists_eq_succ_of_ne_zero
theorem ax4 (a : ℕ) : a + 0 = a := Nat.add_zero a
theorem ax5 (a b : ℕ) : a + (b + 1) = (a + b) + 1 := Nat.add_succ a b
theorem ax6 (a : ℕ) : a * 0 = 0 := Nat.mul_zero a
theorem ax7 (a b : ℕ) : a * (b + 1) = a * b + a := Nat.mul_succ a b

end RobinsonArithmetic

namespace PresburgerArithmetic

/-- A Presburger sentence decided by `omega`: no natural solves `2x + 1 = 2y`. -/
theorem no_odd_even (x y : ℕ) : 2 * x + 1 ≠ 2 * y := by omega

end PresburgerArithmetic
