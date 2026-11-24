module

public import MathTree.MLISP
public import Mathlib.Computability.TuringMachine.Config
public import Mathlib.Computability.PartrecBasis

/-!
# mLISP is Turing complete

We prove that mLISP computes every partial recursive function, by writing a *universal* mLISP
program `U` that interprets the language `Turing.ToPartrec.Code` of Mathlib (`zero'`, `succ`,
`tail`, `cons`, `comp`, `case`, `fix` on lists of naturals), whose semantics `Code.eval` is proved
in Mathlib to capture all partial recursive functions (`Turing.ToPartrec.Code.exists_code`).
Because `U` is a single fixed program, no supply of fresh symbol names is needed: the table
`defsU` has the one entry `U`, and the code to run is passed as *data*.

* `enc l` is the list `[x₁, …, xₙ]` of naturals as the value `{num x₁, {…, {num xₙ, 0}}}`.
* `encCode c` is a code as the value `{num tag, payload}` (tags `0`–`6` for the seven
  constructors, payload the encoded subcodes).
* `U` (two arguments: `i` the code, `j` the input) dispatches on the tag and runs the branch
  `branch c`; `defsU` is the definition table `{U}`; `ComputesIn defs c args v` is `Computes`
  with an arbitrary table.
* `eval_sound`: if `x ∈ c.eval l` then `U [encCode c, enc l] ⇓ enc x` (induction on `c`, with
  `PFun.fixInduction` for `fix`).
* `eval_complete`: if `U [encCode c, enc l] ⇓ v` then `c.eval l` is defined with a value `x` and
  `v = enc x` (via the relation `Sem`, `Eval` with the recursive calls replaced by `Code.eval`).
* `code_computes_iff`, `code_dom_iff`: `U` computes exactly `Code.eval`, and halts exactly when
  it is defined.
* `turing_complete`: for every `Nat.Partrec f` there is a value `cv` such that
  `U [cv, enc [n]]` halts iff `f n` is defined, and `U [cv, enc [n]] ⇓ enc [m]` iff `f n = m`.
* Conversely (`ComputesIn_iff_evalF`, `Computes_iff_run`), `Eval` is the unbounded search over the
  fuel of the total, structurally recursive evaluator `evalF`, so every mLISP-computable partial
  function is partial recursive (see the remark at the end).
-/

@[expose] public section

namespace MLISP

open Turing.ToPartrec (Code)

/-! ## Running programs with an arbitrary definition table -/

/-- `ComputesIn defs c args v`: with the definitions `defs`, the symbol `c` on `args` yields `v`. -/
def ComputesIn (defs : Char → Option E) (c : Char) (args : List V) (v : V) : Prop :=
  ∃ e, defs c = some e ∧ Eval defs e args e v

theorem ComputesIn.det {defs : Char → Option E} {c : Char} {args : List V} {v w : V}
    (h₁ : ComputesIn defs c args v) (h₂ : ComputesIn defs c args w) : v = w := by
  obtain ⟨e, he, h₁⟩ := h₁
  obtain ⟨e', he', h₂⟩ := h₂
  cases Option.some.inj (he.symm.trans he')
  exact Eval.det h₁ h₂

/-! ## Encoding lists of naturals and codes -/

/-- A list of naturals as nested pairs ending in the atom. -/
def enc : List ℕ → V
  | [] => .atom
  | x :: l => .pair (num x) (enc l)

@[simp] theorem enc_nil : enc [] = .atom := rfl
@[simp] theorem enc_cons (x : ℕ) (l : List ℕ) : enc (x :: l) = .pair (num x) (enc l) := rfl

theorem enc_injective : Function.Injective enc := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all
  | cons x l ih =>
    intro l' h
    cases l' with
    | nil => simp at h
    | cons y l' =>
      simp only [enc_cons, V.pair.injEq] at h
      rw [num_injective h.1, ih h.2]

/-- A code as a value: `{num tag, payload}`, the payload being the pair of the encoded
subcodes (or the encoded subcode for `fix`, or the atom). -/
def encCode : Code → V
  | .zero' => .pair (num 0) .atom
  | .succ => .pair (num 1) .atom
  | .tail => .pair (num 2) .atom
  | .cons f g => .pair (num 3) (.pair (encCode f) (encCode g))
  | .comp f g => .pair (num 4) (.pair (encCode f) (encCode g))
  | .case f g => .pair (num 5) (.pair (encCode f) (encCode g))
  | .fix f => .pair (num 6) (encCode f)

/-- The tag of a code. -/
def tag : Code → ℕ
  | .zero' => 0
  | .succ => 1
  | .tail => 2
  | .cons _ _ => 3
  | .comp _ _ => 4
  | .case _ _ => 5
  | .fix _ => 6

/-- The payload of a code. -/
def payload : Code → V
  | .zero' => .atom
  | .succ => .atom
  | .tail => .atom
  | .cons f g => .pair (encCode f) (encCode g)
  | .comp f g => .pair (encCode f) (encCode g)
  | .case f g => .pair (encCode f) (encCode g)
  | .fix f => encCode f

theorem encCode_eq (c : Code) : encCode c = .pair (num (tag c)) (payload c) := by
  cases c <;> rfl

/-! ## The universal program -/

open E in
/-- Head of an encoded list (`0` for the empty list): `d x (a x) 0`. -/
def hd (x : E) : E := d x (a x) zero

open E in
/-- Tail of an encoded list (`0` for the empty list): `d x (b x) 0`. -/
def tl (x : E) : E := d x (b x) zero

open E in
/-- `tagE k` is `b^k (a i)`: the tag of the code `i` with `k` subtracted. -/
def tagE : ℕ → E
  | 0 => a i
  | k + 1 => b (tagE k)

open E in
/-- The branch of `U` for each constructor of `Code`. `i` is the code, `j` the input list. -/
def branch : Code → E
  | .zero' => c zero j
  | .succ => c (c zero (hd j)) zero
  | .tail => tl j
  | .cons _ _ => c (hd (self [a (b i), j])) (self [b (b i), j])
  | .comp _ _ => self [a (b i), self [b (b i), j]]
  | .case _ _ => d j (d (a j) (self [b (b i), c (b (a j)) (b j)]) (self [a (b i), b j]))
      (self [a (b i), zero])
  | .fix _ => d (hd (self [b i, j])) (self [i, tl (self [b i, j])]) (tl (self [b i, j]))

open E in
/-- The universal program: dispatch on the tag of the code `i`, then run the branch. -/
def U : E :=
  d (tagE 0) (d (tagE 1) (d (tagE 2) (d (tagE 3) (d (tagE 4) (d (tagE 5)
    (branch (.fix .zero')) (branch (.case .zero' .zero')))
    (branch (.comp .zero' .zero'))) (branch (.cons .zero' .zero'))) (branch .tail))
    (branch .succ)) (branch .zero')

/-- The definition table: the single symbol `U`. -/
def defsU : Char → Option E
  | 'U' => some U
  | _ => none

/-! ## Evaluation lemmas -/

namespace Eval
variable {defs : Char → Option E} {body : E} {env : List V}

theorem hd {x : E} {l : List ℕ} (h : Eval defs body env x (enc l)) :
    Eval defs body env (MLISP.hd x) (num l.headI) := by
  cases l with
  | nil => exact .dF h .zero
  | cons n l => exact .dT h (.a h)

theorem tl {x : E} {l : List ℕ} (h : Eval defs body env x (enc l)) :
    Eval defs body env (MLISP.tl x) (enc l.tail) := by
  cases l with
  | nil => exact .dF h .zero
  | cons n l => exact .dT h (.b h)

theorem tagE {c : Code} {w : V} (k : ℕ) (hk : k ≤ tag c) :
    Eval defs body (encCode c :: w :: env) (MLISP.tagE k) (num (tag c - k)) := by
  induction k with
  | zero => rw [encCode_eq]; exact .a (.arg rfl)
  | succ k ih =>
    have := ih (Nat.le_of_succ_le hk)
    rw [show tag c - k = (tag c - (k + 1)) + 1 by omega] at this
    exact .b this

end Eval

/-- Dispatch: running `U` on a code amounts to running its branch. -/
theorem Eval.U_of_branch {c : Code} {w v : V} {env : List V}
    (h : Eval defsU U (encCode c :: w :: env) (branch c) v) :
    Eval defsU U (encCode c :: w :: env) U v := by
  have t : ∀ k, k < tag c →
      Eval defsU U (encCode c :: w :: env) (MLISP.tagE k) (.pair .atom (num (tag c - k - 1))) := by
    intro k hk
    have := Eval.tagE (defs := defsU) (body := U) (env := env) (c := c) (w := w) k hk.le
    rwa [show tag c - k = (tag c - k - 1) + 1 by omega] at this
  have t0 : Eval defsU U (encCode c :: w :: env) (MLISP.tagE (tag c)) .atom := by
    simpa using Eval.tagE (defs := defsU) (body := U) (env := env) (c := c) (w := w) (tag c) le_rfl
  cases c with
  | zero' => exact .dF t0 h
  | succ => exact .dT (t 0 (by simp [tag])) (.dF t0 h)
  | tail => exact .dT (t 0 (by simp [tag])) (.dT (t 1 (by simp [tag])) (.dF t0 h))
  | cons f g => exact .dT (t 0 (by simp [tag])) (.dT (t 1 (by simp [tag])) (.dT (t 2 (by simp [tag])) (.dF t0 h)))
  | comp f g =>
    exact .dT (t 0 (by simp [tag])) (.dT (t 1 (by simp [tag])) (.dT (t 2 (by simp [tag]))
      (.dT (t 3 (by simp [tag])) (.dF t0 h))))
  | case f g =>
    exact .dT (t 0 (by simp [tag])) (.dT (t 1 (by simp [tag])) (.dT (t 2 (by simp [tag]))
      (.dT (t 3 (by simp [tag])) (.dT (t 4 (by simp [tag])) (.dF t0 h)))))
  | fix f =>
    exact .dT (t 0 (by simp [tag])) (.dT (t 1 (by simp [tag])) (.dT (t 2 (by simp [tag]))
      (.dT (t 3 (by simp [tag])) (.dT (t 4 (by simp [tag])) (.dT (t 5 (by simp [tag])) h)))))

/-! ## Soundness: `U` computes `Code.eval` -/

theorem eval_sound : ∀ (c : Code) (l x : List ℕ), x ∈ c.eval l →
    Eval defsU U [encCode c, enc l] U (enc x) := by
  intro c
  induction c with
  | zero' =>
    intro l x hx
    simp only [Code.zero'_eval, Part.pure_eq_some, Part.mem_some_iff] at hx
    subst hx
    exact .U_of_branch (.c .zero .j)
  | succ =>
    intro l x hx
    simp only [Code.succ_eval, Part.pure_eq_some, Part.mem_some_iff] at hx
    subst hx
    exact .U_of_branch (.c (.c .zero (Eval.hd .j)) .zero)
  | tail =>
    intro l x hx
    simp only [Code.tail_eval, Part.pure_eq_some, Part.mem_some_iff] at hx
    subst hx
    exact .U_of_branch (Eval.tl .j)
  | cons f g ihf ihg =>
    intro l x hx
    simp only [Code.cons_eval, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
      Part.mem_some_iff] at hx
    obtain ⟨n, hn, ns, hns, rfl⟩ := hx
    exact .U_of_branch (.c (Eval.hd (.self (.two (.a (.b .i)) .j) (ihf l n hn)))
      (.self (.two (.b (.b .i)) .j) (ihg l ns hns)))
  | comp f g ihf ihg =>
    intro l x hx
    rw [Code.comp_eval] at hx
    obtain ⟨y, hy, hx⟩ := Part.mem_bind_iff.1 hx
    exact .U_of_branch (.self (.two (.a (.b .i)) (.self (.two (.b (.b .i)) .j) (ihg l y hy)))
      (ihf y x hx))
  | case f g ihf ihg =>
    intro l x hx
    simp only [Code.case_eval] at hx
    cases l with
    | nil =>
      change x ∈ f.eval [] at hx
      exact .U_of_branch (.dF .j (.self (.two (.a (.b .i)) .zero) (ihf [] x hx)))
    | cons n t =>
      cases n with
      | zero =>
        change x ∈ f.eval t at hx
        exact .U_of_branch (.dT .j (.dF (.a .j) (.self (.two (.a (.b .i)) (.b .j)) (ihf t x hx))))
      | succ m =>
        change x ∈ g.eval (m :: t) at hx
        exact .U_of_branch (.dT .j (.dT (.a .j)
          (.self (.two (.b (.b .i)) (.c (.b (.a .j)) (.b .j))) (ihg (m :: t) x hx))))
  | fix f ih =>
    intro l x hx
    simp only [Code.fix_eval] at hx
    refine PFun.fixInduction hx fun l hl ih' => ?_
    rcases PFun.mem_fix_iff.1 hl with h | ⟨l', hl', _⟩
    · obtain ⟨w, hw, hwx⟩ := (Part.mem_map_iff _).1 h
      split_ifs at hwx with h0
      cases hwx
      have hW : Eval defsU U [encCode (.fix f), enc l] (.self [.b .i, .j]) (enc w) :=
        .self (.two (.b .i) .j) (ih l w hw)
      have hh := Eval.hd hW
      rw [h0] at hh
      exact .U_of_branch (.dF hh (Eval.tl hW))
    · obtain ⟨w, hw, hwx⟩ := (Part.mem_map_iff _).1 hl'
      split_ifs at hwx with h0
      cases hwx
      have hW : Eval defsU U [encCode (.fix f), enc l] (.self [.b .i, .j]) (enc w) :=
        .self (.two (.b .i) .j) (ih l w hw)
      have hh := Eval.hd hW
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero h0
      rw [hm] at hh
      exact .U_of_branch (.dT hh (.self (.two .i (Eval.tl hW)) (ih' _ hl')))

/-! ## Completeness: `U` computes nothing else

To show that `U` terminates only when `Code.eval` is defined, we define `Sem`, the relation
"`e` evaluates to `v`" in which every recursive call `f` (and every call of a defined symbol) is
interpreted by `Code.eval` rather than by running `U` again: a call on arguments
`[encCode c, enc l]` must return `enc x` with `x ∈ c.eval l`, and a call on anything else is
unconstrained. Every derivation of `Eval defsU U` becomes a derivation of `Sem`
(`Eval.sem`, by induction on the derivation), and `Sem` on `U` is inverted by hand
(`Sem.U_inv`). -/

/-- The specification of a recursive call: on `[encCode c, enc l]` the result is `enc x` for some
`x ∈ c.eval l`. -/
def CallSpec (vs : List V) (v : V) : Prop :=
  ∀ c l, vs = [encCode c, enc l] → ∃ x ∈ c.eval l, v = enc x

mutual
  /-- `Eval` with the recursive calls interpreted by `Code.eval`. -/
  inductive Sem : List V → E → V → Prop
    | zero {env} : Sem env .zero .atom
    | arg {env n v} (h : env[n]? = some v) : Sem env (.arg n) v
    | a {env x u w} (h : Sem env x (.pair u w)) : Sem env (.a x) u
    | b {env x u w} (h : Sem env x (.pair u w)) : Sem env (.b x) w
    | c {env x y u w} (hx : Sem env x u) (hy : Sem env y w) : Sem env (.c x y) (.pair u w)
    | dT {env x y z u w v} (hx : Sem env x (.pair u w)) (hy : Sem env y v) : Sem env (.d x y z) v
    | dF {env x y z v} (hx : Sem env x .atom) (hz : Sem env z v) : Sem env (.d x y z) v
    | self {env args vs v} (hargs : SemList env args vs) (h : CallSpec vs v) :
        Sem env (.self args) v
    | call {env name args vs v} (hargs : SemList env args vs) (h : CallSpec vs v) :
        Sem env (.call name args) v

  /-- `Sem` for a list of argument expressions. -/
  inductive SemList : List V → List E → List V → Prop
    | nil {env} : SemList env [] []
    | cons {env x xs v vs} (h : Sem env x v) (hs : SemList env xs vs) :
        SemList env (x :: xs) (v :: vs)
end

theorem defsU_eq {name : Char} {e : E} (h : defsU name = some e) : e = U := by
  unfold defsU at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h (by simp)

/-! ### Inversion lemmas for `Sem` -/

namespace Sem
variable {env : List V} {v : V}

theorem zero_iff : Sem env .zero v ↔ v = .atom :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .zero⟩

theorem arg_iff {n : ℕ} : Sem env (.arg n) v ↔ env[n]? = some v :=
  ⟨fun h => by cases h; assumption, .arg⟩

theorem a_iff {x : E} : Sem env (.a x) v ↔ ∃ w, Sem env x (.pair v w) :=
  ⟨fun h => by cases h; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => .a h⟩

theorem b_iff {x : E} : Sem env (.b x) v ↔ ∃ u, Sem env x (.pair u v) :=
  ⟨fun h => by cases h; exact ⟨_, ‹_›⟩, fun ⟨_, h⟩ => .b h⟩

theorem c_iff {x y : E} : Sem env (.c x y) v ↔ ∃ u w, Sem env x u ∧ Sem env y w ∧ v = .pair u w :=
  ⟨fun h => by cases h; exact ⟨_, _, ‹_›, ‹_›, rfl⟩, fun ⟨_, _, hx, hy, h⟩ => h ▸ .c hx hy⟩

theorem d_iff {x y z : E} : Sem env (.d x y z) v ↔
    (∃ u w, Sem env x (.pair u w) ∧ Sem env y v) ∨ (Sem env x .atom ∧ Sem env z v) :=
  ⟨fun h => by
    cases h
    · exact .inl ⟨_, _, ‹_›, ‹_›⟩
    · exact .inr ⟨‹_›, ‹_›⟩,
   fun h => by
    rcases h with ⟨_, _, hx, hy⟩ | ⟨hx, hz⟩
    · exact .dT hx hy
    · exact .dF hx hz⟩

theorem self_iff {args : List E} :
    Sem env (.self args) v ↔ ∃ vs, SemList env args vs ∧ CallSpec vs v :=
  ⟨fun h => by cases h; exact ⟨_, ‹_›, ‹_›⟩, fun ⟨_, hargs, h⟩ => .self hargs h⟩

theorem call_iff {name : Char} {args : List E} :
    Sem env (.call name args) v ↔ ∃ vs, SemList env args vs ∧ CallSpec vs v :=
  ⟨fun h => by cases h; exact ⟨_, ‹_›, ‹_›⟩, fun ⟨_, hargs, h⟩ => .call hargs h⟩

end Sem

namespace SemList
variable {env : List V} {vs : List V}

theorem nil_iff : SemList env [] vs ↔ vs = [] :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .nil⟩

theorem cons_iff {x : E} {xs : List E} :
    SemList env (x :: xs) vs ↔ ∃ u us, Sem env x u ∧ SemList env xs us ∧ vs = u :: us :=
  ⟨fun h => by cases h; exact ⟨_, _, ‹_›, ‹_›, rfl⟩, fun ⟨_, _, h, hs, e⟩ => e ▸ .cons h hs⟩

end SemList

/-! ### Inverting `U` -/

/-- The value of `tagE k` on a code: defined iff `k ≤ tag c`, and then `num (tag c - k)`. -/
theorem Sem.tagE_iff {c : Code} {w : V} {env : List V} {v : V} (k : ℕ) :
    Sem (encCode c :: w :: env) (tagE k) v ↔ k ≤ tag c ∧ v = num (tag c - k) := by
  induction k generalizing v with
  | zero =>
    simp only [tagE, Sem.a_iff, Sem.arg_iff, List.getElem?_cons_zero, Option.some.injEq,
      encCode_eq, Nat.zero_le, true_and, Nat.sub_zero]
    constructor
    · rintro ⟨w', h⟩; exact (V.pair.inj h).1.symm
    · rintro rfl; exact ⟨_, rfl⟩
  | succ k ih =>
    simp only [tagE, Sem.b_iff, ih]
    constructor
    · rintro ⟨u, hk, h⟩
      obtain ⟨m, hm⟩ : ∃ m, tag c - k = m + 1 := by
        rcases Nat.eq_zero_or_pos (tag c - k) with h0 | h0
        · rw [h0] at h; cases h
        · exact ⟨_, (Nat.succ_pred_eq_of_pos h0).symm⟩
      rw [hm, num_succ] at h
      refine ⟨by omega, ?_⟩
      rw [(V.pair.inj h).2, show tag c - (k + 1) = m by omega]
    · rintro ⟨hk, rfl⟩
      refine ⟨.atom, by omega, ?_⟩
      rw [show tag c - k = (tag c - (k + 1)) + 1 by omega, num_succ]

/-- Dispatch, inverted: `Sem` on `U` is `Sem` on the branch of the code. -/
theorem Sem.branch_of_U {c : Code} {w v : V} {env : List V}
    (h : Sem (encCode c :: w :: env) U v) : Sem (encCode c :: w :: env) (branch c) v := by
  cases c <;> simp [U, Sem.d_iff, Sem.tagE_iff, tag, num] at h <;> exact h


theorem CallSpec.elim {c : Code} {l : List ℕ} {v : V} (h : CallSpec [encCode c, enc l] v) :
    ∃ x ∈ c.eval l, v = enc x :=
  h c l rfl

namespace Sem
variable {env : List V}

/-- A `self` call whose arguments are known to be `[encCode c, enc l]`. -/
theorem self_of {args : List E} {c : Code} {l : List ℕ} {w : V}
    (hargs : ∀ vs, SemList env args vs → vs = [encCode c, enc l])
    (h : Sem env (.self args) w) : ∃ x ∈ c.eval l, w = enc x := by
  obtain ⟨vs, hvs, hspec⟩ := Sem.self_iff.1 h
  exact hspec c l (hargs vs hvs)

/-- Values of a `self` call with known arguments are unique. -/
theorem self_unique {args : List E} {c : Code} {l : List ℕ} {x : List ℕ}
    (hargs : ∀ vs, SemList env args vs → vs = [encCode c, enc l]) (hx : x ∈ c.eval l) :
    ∀ w, Sem env (.self args) w → w = enc x := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := self_of hargs hw
  rw [Part.mem_unique hy hx]

theorem hd_of {x : E} {l : List ℕ} {u : V} (hx : ∀ w, Sem env x w → w = enc l)
    (h : Sem env (MLISP.hd x) u) : u = num l.headI := by
  rcases Sem.d_iff.1 h with ⟨u', w', h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨w'', h2⟩ := Sem.a_iff.1 h2
    have e := hx _ h2
    cases l with
    | nil => cases e
    | cons n t => exact (V.pair.inj e).1
  · have e := hx _ h1
    cases l with
    | nil => exact Sem.zero_iff.1 h2
    | cons n t => cases e

theorem tl_of {x : E} {l : List ℕ} {u : V} (hx : ∀ w, Sem env x w → w = enc l)
    (h : Sem env (MLISP.tl x) u) : u = enc l.tail := by
  rcases Sem.d_iff.1 h with ⟨u', w', h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨u'', h2⟩ := Sem.b_iff.1 h2
    have e := hx _ h2
    cases l with
    | nil => cases e
    | cons n t => exact (V.pair.inj e).2
  · have e := hx _ h1
    cases l with
    | nil => exact Sem.zero_iff.1 h2
    | cons n t => cases e

/-- Some value of `x` can be read off from a value of `hd x`. -/
theorem of_hd {x : E} {u : V} (h : Sem env (MLISP.hd x) u) : ∃ w, Sem env x w := by
  rcases Sem.d_iff.1 h with ⟨_, _, h1, _⟩ | ⟨h1, _⟩ <;> exact ⟨_, h1⟩

theorem hd_self {args : List E} {c : Code} {l : List ℕ} {u : V}
    (hargs : ∀ vs, SemList env args vs → vs = [encCode c, enc l])
    (h : Sem env (MLISP.hd (.self args)) u) : ∃ x ∈ c.eval l, u = num x.headI := by
  obtain ⟨w, hw⟩ := of_hd h
  obtain ⟨x, hx, rfl⟩ := self_of hargs hw
  exact ⟨x, hx, hd_of (self_unique hargs hx) h⟩

end Sem

/-- `Sem` on `U` for a code and a list gives a value of `Code.eval`. -/
theorem Sem.U_inv {c : Code} {l : List ℕ} {v : V} (h : Sem [encCode c, enc l] U v) :
    ∃ x ∈ c.eval l, v = enc x := by
  have hj : ∀ w, Sem [encCode c, enc l] .j w → w = enc l := fun w hw => by
    have := Sem.arg_iff.1 hw
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at this
    exact this.symm
  have h := Sem.branch_of_U h
  cases c with
  | zero' =>
    simp only [branch, Sem.c_iff, Sem.zero_iff] at h
    obtain ⟨u, w, rfl, hw, rfl⟩ := h
    exact ⟨0 :: l, by simp, by rw [hj _ hw]; rfl⟩
  | succ =>
    simp only [branch, Sem.c_iff, Sem.zero_iff] at h
    obtain ⟨u, w, ⟨u', w', rfl, hw', rfl⟩, rfl, rfl⟩ := h
    rw [Sem.hd_of hj hw']
    exact ⟨[l.headI + 1], by simp, rfl⟩
  | tail =>
    rw [Sem.tl_of hj h]
    exact ⟨l.tail, by simp, rfl⟩
  | cons f g =>
    have hf : ∀ vs, SemList [encCode (.cons f g), enc l] [.a (.b .i), .j] vs →
        vs = [encCode f, enc l] := by
      intro vs hvs
      simp [SemList.cons_iff, SemList.nil_iff, Sem.a_iff, Sem.b_iff, Sem.arg_iff, encCode] at hvs
      exact hvs
    have hg : ∀ vs, SemList [encCode (.cons f g), enc l] [.b (.b .i), .j] vs →
        vs = [encCode g, enc l] := by
      intro vs hvs
      simp [SemList.cons_iff, SemList.nil_iff, Sem.b_iff, Sem.arg_iff, encCode] at hvs
      exact hvs
    simp only [branch, Sem.c_iff] at h
    obtain ⟨u, w, hu, hw, rfl⟩ := h
    obtain ⟨n, hn, rfl⟩ := Sem.hd_self hf hu
    obtain ⟨ns, hns, rfl⟩ := Sem.self_of hg hw
    refine ⟨n.headI :: ns, ?_, rfl⟩
    simp only [Code.cons_eval, Part.bind_eq_bind, Part.mem_bind_iff, Part.pure_eq_some,
      Part.mem_some_iff]
    exact ⟨n, hn, ns, hns, rfl⟩
  | comp f g =>
    have hg : ∀ vs, SemList [encCode (.comp f g), enc l] [.b (.b .i), .j] vs →
        vs = [encCode g, enc l] := by
      intro vs hvs
      simp [SemList.cons_iff, SemList.nil_iff, Sem.b_iff, Sem.arg_iff, encCode] at hvs
      exact hvs
    simp only [branch] at h
    obtain ⟨vs, hvs, hspec⟩ := Sem.self_iff.1 h
    obtain ⟨u, us, hu, hus, rfl⟩ := SemList.cons_iff.1 hvs
    obtain ⟨w, ws, hw, hws, rfl⟩ := SemList.cons_iff.1 hus
    cases SemList.nil_iff.1 hws
    obtain ⟨y, hy, rfl⟩ := Sem.self_of hg hw
    have hu' : u = encCode f := by
      obtain ⟨w', hu⟩ := Sem.a_iff.1 hu
      obtain ⟨u', hu⟩ := Sem.b_iff.1 hu
      have := Sem.arg_iff.1 hu
      simp only [List.getElem?_cons_zero, Option.some.injEq, encCode, V.pair.injEq] at this
      exact this.2.1.symm
    subst hu'
    obtain ⟨x, hx, rfl⟩ := hspec.elim
    refine ⟨x, ?_, rfl⟩
    rw [Code.comp_eval]
    exact Part.mem_bind_iff.2 ⟨y, hy, hx⟩
  | case f g =>
    have hf : ∀ (e : E) (l' : List ℕ), (∀ w, Sem [encCode (.case f g), enc l] e w → w = enc l') →
        ∀ vs, SemList [encCode (.case f g), enc l] [.a (.b .i), e] vs →
        vs = [encCode f, enc l'] := by
      intro e l' he vs hvs
      obtain ⟨u, us, hu, hus, rfl⟩ := SemList.cons_iff.1 hvs
      obtain ⟨w, ws, hw, hws, rfl⟩ := SemList.cons_iff.1 hus
      cases SemList.nil_iff.1 hws
      rw [he _ hw]
      simp [Sem.a_iff, Sem.b_iff, Sem.arg_iff, encCode] at hu
      rw [hu]
    have hg : ∀ (e : E) (l' : List ℕ), (∀ w, Sem [encCode (.case f g), enc l] e w → w = enc l') →
        ∀ vs, SemList [encCode (.case f g), enc l] [.b (.b .i), e] vs →
        vs = [encCode g, enc l'] := by
      intro e l' he vs hvs
      obtain ⟨u, us, hu, hus, rfl⟩ := SemList.cons_iff.1 hvs
      obtain ⟨w, ws, hw, hws, rfl⟩ := SemList.cons_iff.1 hus
      cases SemList.nil_iff.1 hws
      rw [he _ hw]
      simp [Sem.b_iff, Sem.arg_iff, encCode] at hu
      rw [hu]
    simp only [branch] at h
    rcases Sem.d_iff.1 h with ⟨u, w, h1, h2⟩ | ⟨h1, h2⟩
    · have e := hj _ h1
      cases l with
      | nil => cases e
      | cons n t =>
        obtain ⟨rfl, rfl⟩ := V.pair.inj e
        rcases Sem.d_iff.1 h2 with ⟨u', w', h3, h4⟩ | ⟨h3, h4⟩
        · obtain ⟨w'', h3⟩ := Sem.a_iff.1 h3
          have e := hj _ h3
          cases n with
          | zero => cases (V.pair.inj e).1
          | succ m =>
            obtain ⟨e1, rfl⟩ := V.pair.inj e
            obtain ⟨rfl, rfl⟩ := V.pair.inj e1
            have harg : ∀ w, Sem [encCode (.case f g), enc ((m + 1) :: t)]
                (.c (.b (.a .j)) (.b .j)) w → w = enc (m :: t) := by
              intro w hw
              obtain ⟨u, w', hu, hw', rfl⟩ := Sem.c_iff.1 hw
              obtain ⟨u', hu⟩ := Sem.b_iff.1 hu
              obtain ⟨w₂, hu⟩ := Sem.a_iff.1 hu
              obtain ⟨u₂, hw'⟩ := Sem.b_iff.1 hw'
              have e1 := hj _ hu
              have e2 := hj _ hw'
              obtain ⟨e1, -⟩ := V.pair.inj e1
              obtain ⟨-, e2⟩ := V.pair.inj e2
              obtain ⟨-, rfl⟩ := V.pair.inj e1
              rw [e2]; rfl
            obtain ⟨x, hx, rfl⟩ := Sem.self_of (hg _ _ harg) h4
            exact ⟨x, by simpa [Code.case_eval] using hx, rfl⟩
        · obtain ⟨w'', h3⟩ := Sem.a_iff.1 h3
          have e := hj _ h3
          cases n with
          | succ m => cases (V.pair.inj e).1
          | zero =>
            have harg : ∀ w, Sem [encCode (.case f g), enc (0 :: t)] (.b .j) w → w = enc t := by
              intro w hw
              obtain ⟨u', hw⟩ := Sem.b_iff.1 hw
              exact (V.pair.inj (hj _ hw)).2
            obtain ⟨x, hx, rfl⟩ := Sem.self_of (hf _ _ harg) h4
            exact ⟨x, by simpa [Code.case_eval] using hx, rfl⟩
    · have e := hj _ h1
      cases l with
      | cons n t => cases e
      | nil =>
        have harg : ∀ w, Sem [encCode (.case f g), enc []] .zero w → w = enc [] :=
          fun w hw => Sem.zero_iff.1 hw
        obtain ⟨x, hx, rfl⟩ := Sem.self_of (hf _ _ harg) h2
        exact ⟨x, by simpa [Code.case_eval] using hx, rfl⟩
  | fix f =>
    have hfa : ∀ vs, SemList [encCode (.fix f), enc l] [.b .i, .j] vs → vs = [encCode f, enc l] := by
      intro vs hvs
      simp [SemList.cons_iff, SemList.nil_iff, Sem.b_iff, Sem.arg_iff, encCode] at hvs
      exact hvs
    simp only [branch] at h
    rcases Sem.d_iff.1 h with ⟨u, w, h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨x, hx, e⟩ := Sem.hd_self hfa h1
      have hxw := Sem.self_unique hfa hx
      have h0 : x.headI ≠ 0 := by
        intro h0; rw [h0] at e; cases e
      have harg : ∀ vs, SemList [encCode (.fix f), enc l] [.i, MLISP.tl (.self [.b .i, .j])] vs →
          vs = [encCode (.fix f), enc x.tail] := by
        intro vs hvs
        obtain ⟨u, us, hu, hus, rfl⟩ := SemList.cons_iff.1 hvs
        obtain ⟨w, ws, hw, hws, rfl⟩ := SemList.cons_iff.1 hus
        cases SemList.nil_iff.1 hws
        rw [Sem.tl_of hxw hw]
        have := Sem.arg_iff.1 hu
        simp only [List.getElem?_cons_zero, Option.some.injEq] at this
        rw [this]
      obtain ⟨y, hy, rfl⟩ := Sem.self_of harg h2
      refine ⟨y, ?_, rfl⟩
      rw [Code.fix_eval] at hy ⊢
      refine PFun.mem_fix_iff.2 (Or.inr ⟨x.tail, ?_, hy⟩)
      exact (Part.mem_map_iff _).2 ⟨x, hx, by simp [h0]⟩
    · obtain ⟨x, hx, e⟩ := Sem.hd_self hfa h1
      have hxw := Sem.self_unique hfa hx
      have h0 : x.headI = 0 := by
        cases hh : x.headI with
        | zero => rfl
        | succ m => rw [hh] at e; cases e
      rw [Sem.tl_of hxw h2]
      refine ⟨x.tail, ?_, rfl⟩
      rw [Code.fix_eval]
      exact PFun.fix_stop ((Part.mem_map_iff _).2 ⟨x, hx, by simp [h0]⟩)

/-! Every `Eval` derivation with body `U` is a `Sem` derivation (by structural recursion on the
derivation; the body is generalized so that the recursion is structural). -/
mutual
  theorem Eval.sem : ∀ {body env e v}, Eval defsU body env e v → body = U → Sem env e v
    | _, _, _, _, .zero, _ => .zero
    | _, _, _, _, .arg h, _ => .arg h
    | _, _, _, _, .a h, hU => .a (Eval.sem h hU)
    | _, _, _, _, .b h, hU => .b (Eval.sem h hU)
    | _, _, _, _, .c hx hy, hU => .c (Eval.sem hx hU) (Eval.sem hy hU)
    | _, _, _, _, .dT hx hy, hU => .dT (Eval.sem hx hU) (Eval.sem hy hU)
    | _, _, _, _, .dF hx hz, hU => .dF (Eval.sem hx hU) (Eval.sem hz hU)
    | _, _, _, _, .self hargs hbody, hU =>
      have ih := Eval.sem hbody hU
      .self (EvalList.sem hargs hU) fun c l e => by
        subst hU; subst e
        exact Sem.U_inv ih
    | _, _, _, _, .call hdef hargs hbody, hU =>
      have ih := Eval.sem hbody (defsU_eq hdef)
      .call (EvalList.sem hargs hU) fun c l e => by
        cases defsU_eq hdef; subst e
        exact Sem.U_inv ih

  theorem EvalList.sem : ∀ {body env xs vs}, EvalList defsU body env xs vs → body = U →
      SemList env xs vs
    | _, _, _, _, .nil, _ => .nil
    | _, _, _, _, .cons h hs, hU => .cons (Eval.sem h hU) (EvalList.sem hs hU)
end

/-- Completeness: if `U` on `[encCode c, enc l]` evaluates to `v`, then `c.eval l` is defined,
with a value `x` such that `v = enc x`. -/
theorem eval_complete {c : Code} {l : List ℕ} {v : V} (h : Eval defsU U [encCode c, enc l] U v) :
    ∃ x ∈ c.eval l, v = enc x :=
  Sem.U_inv (Eval.sem h rfl)

/-- `U` computes exactly `Code.eval`. -/
theorem eval_iff (c : Code) (l x : List ℕ) :
    x ∈ c.eval l ↔ Eval defsU U [encCode c, enc l] U (enc x) :=
  ⟨eval_sound c l x, fun h => by
    obtain ⟨y, hy, e⟩ := eval_complete h
    rw [enc_injective e]; exact hy⟩

/-- `U` computes every `Code`, and nothing else: `U [encCode c, enc l] ⇓ enc x` iff
`x ∈ c.eval l`. -/
theorem code_computes_iff (c : Code) (l x : List ℕ) :
    ComputesIn defsU 'U' [encCode c, enc l] (enc x) ↔ x ∈ c.eval l := by
  constructor
  · rintro ⟨e, he, h⟩
    cases defsU_eq he
    exact (eval_iff c l x).2 h
  · exact fun h => ⟨U, rfl, eval_sound c l x h⟩

/-- `U` on `[encCode c, enc l]` terminates iff `c.eval l` is defined. -/
theorem code_dom_iff (c : Code) (l : List ℕ) :
    (∃ v, ComputesIn defsU 'U' [encCode c, enc l] v) ↔ (c.eval l).Dom := by
  constructor
  · rintro ⟨v, e, he, h⟩
    cases defsU_eq he
    obtain ⟨x, hx, -⟩ := eval_complete h
    exact Part.dom_iff_mem.2 ⟨x, hx⟩
  · intro h
    exact ⟨_, U, rfl, eval_sound c l _ (Part.get_mem h)⟩

/-- mLISP is Turing complete: for every partial recursive `f : ℕ →. ℕ` there is a code value `cv`
such that the universal program `U` on `[cv, enc [n]]` halts iff `f n` is defined, and evaluates
to `enc [m]` exactly when `f n = m`. -/
theorem turing_complete (f : ℕ →. ℕ) (hf : Nat.Partrec f) :
    ∃ cv : V, ∀ n, ((∃ v, ComputesIn defsU 'U' [cv, enc [n]] v) ↔ (f n).Dom) ∧
      ∀ m, ComputesIn defsU 'U' [cv, enc [n]] (enc [m]) ↔ m ∈ f n := by
  obtain ⟨c, hc⟩ := Code.exists_code (Nat.Partrec'.part_iff₁.2 (Partrec.nat_iff.2 hf))
  have key : ∀ n, c.eval [n] = Part.map (fun m => [m]) (f n) := fun n => by
    have h := hc ⟨[n], rfl⟩
    simp only [List.Vector.head, Part.map_eq_map] at h
    exact h
  refine ⟨encCode c, fun n => ⟨?_, fun m => ?_⟩⟩
  · rw [code_dom_iff, key, Part.map_Dom]
  · rw [code_computes_iff, key, Part.mem_map_iff]
    constructor
    · rintro ⟨m', hm', e⟩
      cases List.singleton_inj.1 e
      exact hm'
    · exact fun hm => ⟨m, hm, rfl⟩

/-- The value form of `turing_complete`: whenever `f n = m`, `U [cv, enc [n]] ⇓ enc [m]`. -/
theorem turing_complete_val (f : ℕ →. ℕ) (hf : Nat.Partrec f) :
    ∃ cv : V, ∀ n m, m ∈ f n → ComputesIn defsU 'U' [cv, enc [n]] (enc [m]) :=
  let ⟨cv, h⟩ := turing_complete f hf
  ⟨cv, fun n m hm => ((h n).2 m).2 hm⟩

/-! ## Executable checks -/

/-- Run `U` on a code and an input list with the given fuel. -/
def runU (fuel : ℕ) (c : Code) (l : List ℕ) : Option V :=
  evalF defsU fuel U [encCode c, enc l] U

example : runU 100 (.cons .succ .tail) [3, 4] = some (enc [4, 4]) := by decide
example : runU 100 (.case .zero' .succ) [2, 7] = some (enc [2]) := by decide
example : runU 100 (.case .zero' .succ) [0, 7] = some (enc [0, 7]) := by decide
-- `fix (cons pred (cons pred tail))` maps `[n]` to `[n-1, n-1]` and loops: it counts `n` down
-- to `0`, leaving `[0]`.
example : runU 300 (.fix (.cons .pred (.cons .pred .tail))) [3] = some (enc [0]) := by decide
-- `fix zero'` never stops: the head of `0 :: v` is `0`, so `fix` returns `v`; but `fix succ` does
-- not terminate (`succ` always returns a nonzero head).
example : runU 100 (.fix .zero') [5] = some (enc [5]) := by decide
example : runU 100 (.fix .succ) [5] = none := by decide

/-! ## The converse: mLISP programs are computable

`evalF` is a total function defined by structural recursion on the fuel, hence computable in the
ordinary sense, and the big-step relation is its unbounded search over the fuel
(`ComputesIn_iff_evalF`). So every partial function computed by an mLISP program is partial
recursive: its graph is the projection of a decidable relation. Formalizing this as `Partrec`
would require `Primcodable` instances for `V` and `E` and a `Primrec` proof for `evalF`; we do
not attempt it here. -/

theorem evalArgsWith_mono {f g : E → Option V} (hfg : ∀ x v, f x = some v → g x = some v) :
    ∀ {xs vs}, evalArgsWith f xs = some vs → evalArgsWith g xs = some vs
  | [], _, h => by simpa [evalArgsWith] using h
  | x :: xs, vs, h => by
    simp only [evalArgsWith] at h ⊢
    split at h
    · rename_i v vs' hv hvs
      rw [hfg _ _ hv, evalArgsWith_mono hfg hvs]
      exact h
    · exact absurd h (by simp)

/-- More fuel never changes a defined result. -/
theorem evalF_le {defs : Char → Option E} :
    ∀ {n m : ℕ}, n ≤ m → ∀ {body env e v}, evalF defs n body env e = some v →
      evalF defs m body env e = some v := by
  intro n
  induction n with
  | zero => intro m _ body env e v h; simp [evalF] at h
  | succ n ih =>
    intro m hm body env e v h
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : n ≤ m := by omega
    cases e with
    | zero => simpa [evalF] using h
    | arg k => simpa [evalF] using h
    | a x =>
      simp only [evalF] at h ⊢
      split at h
      · rename_i u w hx; rw [ih hm' hx]; exact h
      · exact absurd h (by simp)
    | b x =>
      simp only [evalF] at h ⊢
      split at h
      · rename_i u w hx; rw [ih hm' hx]; exact h
      · exact absurd h (by simp)
    | c x y =>
      simp only [evalF] at h ⊢
      split at h
      · rename_i u w hx hy; rw [ih hm' hx, ih hm' hy]; exact h
      · exact absurd h (by simp)
    | d x y z =>
      simp only [evalF] at h ⊢
      split at h
      · rename_i u w hx; rw [ih hm' hx]; exact ih hm' h
      · rename_i hx; rw [ih hm' hx]; exact ih hm' h
      · exact absurd h (by simp)
    | call name args =>
      simp only [evalF] at h ⊢
      split at h
      · rename_i e' vs hd hargs
        rw [hd, evalArgsWith_mono (fun _ _ hx => ih hm' hx) hargs]
        exact ih hm' h
      · exact absurd h (by simp)
    | self args =>
      simp only [evalF] at h ⊢
      split at h
      · rename_i vs hargs
        rw [evalArgsWith_mono (fun _ _ hx => ih hm' hx) hargs]
        exact ih hm' h
      · exact absurd h (by simp)

/-! Completeness of the fuel evaluator: every derivation is found with enough fuel. -/
mutual
  theorem Eval.exists_evalF {defs : Char → Option E} :
      ∀ {body env e v}, Eval defs body env e v → ∃ n, evalF defs n body env e = some v
    | _, _, _, _, .zero => ⟨1, rfl⟩
    | _, _, _, _, .arg h => ⟨1, by simpa [evalF] using h⟩
    | _, _, _, _, .a h =>
      let ⟨n, hn⟩ := Eval.exists_evalF h
      ⟨n + 1, by simp [evalF, hn]⟩
    | _, _, _, _, .b h =>
      let ⟨n, hn⟩ := Eval.exists_evalF h
      ⟨n + 1, by simp [evalF, hn]⟩
    | _, _, _, _, .c hx hy =>
      let ⟨n₁, h₁⟩ := Eval.exists_evalF hx
      let ⟨n₂, h₂⟩ := Eval.exists_evalF hy
      ⟨max n₁ n₂ + 1, by
        simp [evalF, evalF_le (le_max_left n₁ n₂) h₁, evalF_le (le_max_right n₁ n₂) h₂]⟩
    | _, _, _, _, .dT hx hy =>
      let ⟨n₁, h₁⟩ := Eval.exists_evalF hx
      let ⟨n₂, h₂⟩ := Eval.exists_evalF hy
      ⟨max n₁ n₂ + 1, by
        simp [evalF, evalF_le (le_max_left n₁ n₂) h₁, evalF_le (le_max_right n₁ n₂) h₂]⟩
    | _, _, _, _, .dF hx hz =>
      let ⟨n₁, h₁⟩ := Eval.exists_evalF hx
      let ⟨n₂, h₂⟩ := Eval.exists_evalF hz
      ⟨max n₁ n₂ + 1, by
        simp [evalF, evalF_le (le_max_left n₁ n₂) h₁, evalF_le (le_max_right n₁ n₂) h₂]⟩
    | _, _, _, _, .self hargs hbody =>
      let ⟨n₁, h₁⟩ := EvalList.exists_evalF hargs
      let ⟨n₂, h₂⟩ := Eval.exists_evalF hbody
      ⟨max n₁ n₂ + 1, by
        simp [evalF, evalArgsWith_mono (fun _ _ h => evalF_le (le_max_left n₁ n₂) h) h₁,
          evalF_le (le_max_right n₁ n₂) h₂]⟩
    | _, _, _, _, .call hdef hargs hbody =>
      let ⟨n₁, h₁⟩ := EvalList.exists_evalF hargs
      let ⟨n₂, h₂⟩ := Eval.exists_evalF hbody
      ⟨max n₁ n₂ + 1, by
        simp [evalF, hdef, evalArgsWith_mono (fun _ _ h => evalF_le (le_max_left n₁ n₂) h) h₁,
          evalF_le (le_max_right n₁ n₂) h₂]⟩

  theorem EvalList.exists_evalF {defs : Char → Option E} :
      ∀ {body env xs vs}, EvalList defs body env xs vs →
        ∃ n, evalArgsWith (evalF defs n body env) xs = some vs
    | _, _, _, _, .nil => ⟨0, rfl⟩
    | _, _, _, _, .cons h hs =>
      let ⟨n₁, h₁⟩ := Eval.exists_evalF h
      let ⟨n₂, h₂⟩ := EvalList.exists_evalF hs
      ⟨max n₁ n₂, by
        simp [evalArgsWith, evalF_le (le_max_left n₁ n₂) h₁,
          evalArgsWith_mono (fun _ _ h => evalF_le (le_max_right n₁ n₂) h) h₂]⟩
end

/-- The big-step relation is the unbounded search over the fuel of the executable evaluator. -/
theorem ComputesIn_iff_evalF {defs : Char → Option E} {c : Char} {args : List V} {v : V} :
    ComputesIn defs c args v ↔
      ∃ fuel e, defs c = some e ∧ evalF defs fuel e args e = some v := by
  constructor
  · rintro ⟨e, he, h⟩
    obtain ⟨n, hn⟩ := Eval.exists_evalF h
    exact ⟨n, e, he, hn⟩
  · rintro ⟨n, e, he, h⟩
    exact ⟨e, he, evalF_sound h⟩

/-- The same for the programs of the website: `Computes c args v ↔ ∃ fuel, run fuel c args = some v`. -/
theorem Computes_iff_run {c : Char} {args : List V} {v : V} :
    Computes c args v ↔ ∃ fuel, run fuel c args = some v := by
  constructor
  · rintro ⟨e, he, h⟩
    obtain ⟨n, hn⟩ := Eval.exists_evalF h
    exact ⟨n, by unfold run; rw [he]; exact hn⟩
  · rintro ⟨n, h⟩
    exact Computes.of_run h

end MLISP
