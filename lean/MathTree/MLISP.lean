module

public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# mLISP: Tegmark's minimal language, and what its standard programs compute

This file formalizes the language mLISP of Section 2.1 of Max Tegmark's document and proves that
the programs of its tables compute what they claim.

**Values** (`V`) are the atom `0` and pairs `{x, y}`. Natural numbers are nested pairs
(`num 0 = 0`, `num (n+1) = {0, num n}`), the atom is "false" and every pair is "true".

**Programs** are postfix strings of single characters. The base symbols and their arities are
`a`(1) first part, `b`(1) second part, `c`(2) pair, `d`(3) decide (if the first argument is a
pair then the second else the third, only the chosen branch being evaluated), `f` the recursive
call of the function being defined, `i j k`(0) the arguments and `0`(0) the atom. A defined
symbol stands for its own program, called with the arguments `i j k`. There is no primitive
equality test: `e` = `ijiajafibjbf0d0dj01dd` is an ordinary program of the table
(`eq_computes` proves that it computes equality).

The formalization has three layers:

* `E` is the expression tree of a program, `parse` turns a program string into it (with a stack,
  exactly as the Python interpreter `mlisp.py` does), and `table` lists the program strings of the
  website; `table_parses` checks (by `rfl`, i.e. by running the parser in the kernel) that every
  string of the table parses to the expression tree the theorems are about.
* `Eval defs body env e v` is the big-step evaluation relation: in the context of the function
  `body` (for `f`) with arguments `env`, the expression `e` evaluates to the value `v`. It is an
  inductive relation, so the laziness of `d` and the undefinedness of `a 0`, `b 0` and of
  non-terminating recursions are built in: there is simply no derivation. `evalF` is a fuel-based
  executable evaluator, proved sound (`evalF_sound`) with respect to `Eval`, so that concrete
  cases can be checked by `decide` / `native_decide`; `Eval.det` shows the relation is a partial
  function, so "the program evaluates to `v`" determines `v`.
* The theorems: `succ_computes`, `plus_computes`, `times_computes`, ... state, for all naturals,
  that the programs of Table 1 compute successor, sum, product, difference, power, factorial, the
  Boolean connectives, `<`, divisibility and primality (`prime_computes`, `prime_iff`);
  `zadd_computes`, `zmul_computes`, ... the same for the integer programs (pairs `{a, b}` standing
  for `a - b`, `zpair` being the canonical pair); `qadd_computes`, `qdiv_computes`, ... the same
  for the rational programs (pairs `{canonical integer, natural ≥ 1}` in lowest terms, `qpair r`
  being the value of `r : ℚ`); `bs_computes`, `bp_computes`, `bm_computes`, `beta_computes`,
  `nu_computes` the same for the binary programs (`bin n` being the list of the bits of `n`, least
  significant first, `β`/`ν` converting between unary and binary, with `bin_injective`).
  Executable tests at the end cross-check the evaluator against Lean's arithmetic.
* A meta-circular evaluator: `ε` (with the helpers `u`, list index, and `λ`, chain of `c`-nodes)
  is an mLISP interpreter written in mLISP, taking the *tree* of an expression (`encE`, every node
  being `{op, {extra, args}}`), the argument list and the list `encD` of the trees of all
  programs of the table (the equality test `e` being an ordinary program, the tree of `e(x, y)`
  is a call node like any other). `Eval.meta` proves by induction on the evaluation derivation
  that `ε` is sound,
  `meta_sound` that `ε` on the tree of any program of the table computes what the program
  computes, and `meta_tests` runs it on `+`, `*`, `Π` and `e`.

Conventions: `Computes c args v` means "calling the symbol `c` of the table on `args` yields `v`";
`num n` is the natural `n`, `boolV b` the Boolean `b` (`num 1` / `num 0`).
-/

@[expose] public section

namespace MLISP

/-! ## Values -/

/-- A value of mLISP: the atom `0` or a pair `{a, b}`. -/
inductive V
  | atom
  | pair (a b : V)
  deriving DecidableEq, Repr

/-- The natural number `n` as nested pairs: `num 0 = 0`, `num (n+1) = {0, num n}`. -/
def num : ℕ → V
  | 0 => .atom
  | n + 1 => .pair .atom (num n)

@[simp] theorem num_zero : num 0 = .atom := rfl
@[simp] theorem num_succ (n : ℕ) : num (n + 1) = .pair .atom (num n) := rfl

/-- Decode a nested-pair natural (`val (num n) = n`); any pair counts as a successor. -/
def val : V → ℕ
  | .atom => 0
  | .pair _ b => val b + 1

@[simp] theorem val_num (n : ℕ) : val (num n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [val, ih]

theorem num_injective : Function.Injective num := fun m n h => by
  simpa using congrArg val h

/-- The Boolean values the programs return: `num 1 = {0, 0}` for true and `num 0 = 0` for false. -/
def boolV : Bool → V
  | true => num 1
  | false => num 0

theorem boolV_congr {p q : Prop} [Decidable p] [Decidable q] (h : p ↔ q) :
    boolV (decide p) = boolV (decide q) := by
  rw [decide_eq_decide.mpr h]

/-! ## Expressions -/

/-- The expression tree of a program. `arg 0`, `arg 1`, `arg 2` are `i`, `j`, `k`; `self args` is
the recursive call `f`; `call name args` is a call of the defined symbol `name`. -/
inductive E
  | zero
  | arg (n : ℕ)
  | a (x : E)
  | b (x : E)
  | c (x y : E)
  | d (x y z : E)
  | call (name : Char) (args : List E)
  | self (args : List E)
  deriving Repr

/-- The arguments `i`, `j`, `k`. -/
abbrev E.i : E := .arg 0
abbrev E.j : E := .arg 1
abbrev E.k : E := .arg 2

/-! ## Big-step evaluation

`Eval defs body env e v`: with the definitions `defs`, inside the function whose program is `body`
(the meaning of `f`), with the arguments `env` (the meaning of `i j k`), the expression `e`
evaluates to the value `v`. -/

mutual
  inductive Eval (defs : Char → Option E) : E → List V → E → V → Prop
    /-- `0` is the atom. -/
    | zero {body env} : Eval defs body env .zero .atom
    /-- `i`, `j`, `k` are the arguments. -/
    | arg {body env n v} (h : env[n]? = some v) : Eval defs body env (.arg n) v
    /-- `a` of a pair is its first part (there is no rule for `a` of the atom). -/
    | a {body env x u w} (h : Eval defs body env x (.pair u w)) : Eval defs body env (.a x) u
    /-- `b` of a pair is its second part. -/
    | b {body env x u w} (h : Eval defs body env x (.pair u w)) : Eval defs body env (.b x) w
    /-- `c` makes a pair. -/
    | c {body env x y u w} (hx : Eval defs body env x u) (hy : Eval defs body env y w) :
        Eval defs body env (.c x y) (.pair u w)
    /-- `d`: if the condition is a pair (true), the value is that of the second argument. -/
    | dT {body env x y z u w v} (hx : Eval defs body env x (.pair u w)) (hy : Eval defs body env y v) :
        Eval defs body env (.d x y z) v
    /-- `d`: if the condition is the atom (false), the value is that of the third argument. -/
    | dF {body env x y z v} (hx : Eval defs body env x .atom) (hz : Eval defs body env z v) :
        Eval defs body env (.d x y z) v
    /-- `f`: evaluate the arguments, then the body of the current function on them. -/
    | self {body env args vs v} (hargs : EvalList defs body env args vs)
        (hbody : Eval defs body vs body v) : Eval defs body env (.self args) v
    /-- A defined symbol: evaluate the arguments, then its program on them (with itself as `f`). -/
    | call {body env name args e vs v} (hdef : defs name = some e)
        (hargs : EvalList defs body env args vs) (hbody : Eval defs e vs e v) :
        Eval defs body env (.call name args) v

  /-- Evaluation of a list of argument expressions, in order. -/
  inductive EvalList (defs : Char → Option E) : E → List V → List E → List V → Prop
    | nil {body env} : EvalList defs body env [] []
    | cons {body env x xs v vs} (h : Eval defs body env x v) (hs : EvalList defs body env xs vs) :
        EvalList defs body env (x :: xs) (v :: vs)
end

namespace Eval
variable {defs : Char → Option E} {body : E} {env : List V}

theorem i {v : V} : Eval defs body (v :: env) .i v := .arg rfl
theorem j {u v : V} : Eval defs body (u :: v :: env) .j v := .arg rfl
theorem k {u v w : V} : Eval defs body (u :: v :: w :: env) .k w := .arg rfl

end Eval

namespace EvalList
variable {defs : Char → Option E} {body : E} {env : List V}

theorem one {x : E} {v : V} (h : Eval defs body env x v) : EvalList defs body env [x] [v] :=
  .cons h .nil
theorem two {x y : E} {u v : V} (hx : Eval defs body env x u) (hy : Eval defs body env y v) :
    EvalList defs body env [x, y] [u, v] :=
  .cons hx (.cons hy .nil)

end EvalList

/-! ### Evaluation is deterministic -/

mutual
  theorem Eval.det {defs : Char → Option E} :
      ∀ {body env e v w}, Eval defs body env e v → Eval defs body env e w → v = w
    | _, _, _, _, _, .zero, .zero => rfl
    | _, _, _, _, _, .arg h₁, .arg h₂ => Option.some.inj (h₁.symm.trans h₂)
    | _, _, _, _, _, .a h₁, .a h₂ => by cases Eval.det h₁ h₂; rfl
    | _, _, _, _, _, .b h₁, .b h₂ => by cases Eval.det h₁ h₂; rfl
    | _, _, _, _, _, .c hx₁ hy₁, .c hx₂ hy₂ => by rw [Eval.det hx₁ hx₂, Eval.det hy₁ hy₂]
    | _, _, _, _, _, .dT _ hy₁, .dT _ hy₂ => Eval.det hy₁ hy₂
    | _, _, _, _, _, .dT hx₁ _, .dF hx₂ _ => by cases Eval.det hx₁ hx₂
    | _, _, _, _, _, .dF hx₁ _, .dT hx₂ _ => by cases Eval.det hx₁ hx₂
    | _, _, _, _, _, .dF _ hz₁, .dF _ hz₂ => Eval.det hz₁ hz₂
    | _, _, _, _, _, .self hl₁ h₁, .self hl₂ h₂ => by
      cases EvalList.det hl₁ hl₂; exact Eval.det h₁ h₂
    | _, _, _, _, _, .call hd₁ hl₁ h₁, .call hd₂ hl₂ h₂ => by
      cases Option.some.inj (hd₁.symm.trans hd₂); cases EvalList.det hl₁ hl₂; exact Eval.det h₁ h₂

  theorem EvalList.det {defs : Char → Option E} :
      ∀ {body env xs vs ws}, EvalList defs body env xs vs → EvalList defs body env xs ws → vs = ws
    | _, _, _, _, _, .nil, .nil => rfl
    | _, _, _, _, _, .cons h₁ hl₁, .cons h₂ hl₂ => by rw [Eval.det h₁ h₂, EvalList.det hl₁ hl₂]
end

/-! ## A fuel-based executable evaluator, sound for `Eval` -/

/-- Evaluate a list of expressions with `f`, failing if any fails. -/
def evalArgsWith (f : E → Option V) : List E → Option (List V)
  | [] => some []
  | x :: xs =>
    match f x, evalArgsWith f xs with
    | some v, some vs => some (v :: vs)
    | _, _ => none

/-- `evalF defs fuel body env e`: the value of `e` (as in `Eval`), or `none` if it is undefined or
needs more than `fuel` nested steps. -/
def evalF (defs : Char → Option E) : ℕ → E → List V → E → Option V
  | 0, _, _, _ => none
  | n + 1, body, env, e =>
    match e with
    | .zero => some .atom
    | .arg k => env[k]?
    | .a x =>
      match evalF defs n body env x with
      | some (.pair u _) => some u
      | _ => none
    | .b x =>
      match evalF defs n body env x with
      | some (.pair _ w) => some w
      | _ => none
    | .c x y =>
      match evalF defs n body env x, evalF defs n body env y with
      | some u, some w => some (.pair u w)
      | _, _ => none
    | .d x y z =>
      match evalF defs n body env x with
      | some (.pair _ _) => evalF defs n body env y
      | some .atom => evalF defs n body env z
      | none => none
    | .call name args =>
      match defs name, evalArgsWith (evalF defs n body env) args with
      | some e', some vs => evalF defs n e' vs e'
      | _, _ => none
    | .self args =>
      match evalArgsWith (evalF defs n body env) args with
      | some vs => evalF defs n body vs body
      | none => none

theorem evalArgsWith_sound {defs : Char → Option E} {body : E} {env : List V} {f : E → Option V}
    (hf : ∀ x v, f x = some v → Eval defs body env x v) :
    ∀ {xs vs}, evalArgsWith f xs = some vs → EvalList defs body env xs vs
  | [], vs, h => by
    simp only [evalArgsWith, Option.some.injEq] at h
    subst h; exact .nil
  | x :: xs, vs, h => by
    simp only [evalArgsWith] at h
    split at h
    · rename_i v vs' hv hvs
      cases h
      exact .cons (hf _ _ hv) (evalArgsWith_sound hf hvs)
    · exact absurd h (by simp)

theorem evalF_sound {defs : Char → Option E} :
    ∀ {n : ℕ} {body env e v}, evalF defs n body env e = some v → Eval defs body env e v := by
  intro n
  induction n with
  | zero => intro body env e v h; simp [evalF] at h
  | succ n ih =>
    intro body env e v h
    cases e with
    | zero => simp only [evalF, Option.some.injEq] at h; subst h; exact .zero
    | arg k => exact .arg (by simpa [evalF] using h)
    | a x =>
      simp only [evalF] at h
      split at h
      · rename_i u w hx; cases h; exact .a (ih hx)
      · exact absurd h (by simp)
    | b x =>
      simp only [evalF] at h
      split at h
      · rename_i u w hx; cases h; exact .b (ih hx)
      · exact absurd h (by simp)
    | c x y =>
      simp only [evalF] at h
      split at h
      · rename_i u w hx hy; cases h; exact .c (ih hx) (ih hy)
      · exact absurd h (by simp)
    | d x y z =>
      simp only [evalF] at h
      split at h
      · rename_i u w hx; exact .dT (ih hx) (ih h)
      · rename_i hx; exact .dF (ih hx) (ih h)
      · exact absurd h (by simp)
    | call name args =>
      simp only [evalF] at h
      split at h
      · rename_i e' vs hd hargs
        exact .call hd (evalArgsWith_sound (fun _ _ hx => ih hx) hargs) (ih h)
      · exact absurd h (by simp)
    | self args =>
      simp only [evalF] at h
      split at h
      · rename_i vs hargs
        exact .self (evalArgsWith_sound (fun _ _ hx => ih hx) hargs) (ih h)
      · exact absurd h (by simp)

/-! ## The parser

A program is read left to right with a stack: a symbol of arity `n` pops its `n` arguments and
pushes the node. The arity of `f` is that of the function being defined (`farity`); the arity of
a defined symbol is the highest of `i j k` used in its program (`textArity`), as in `programs.py`.
-/

/-- Arities of the base symbols. -/
def baseArity : Char → Option ℕ
  | 'a' => some 1
  | 'b' => some 1
  | 'c' => some 2
  | 'd' => some 3
  | '0' => some 0
  | 'i' => some 0
  | 'j' => some 0
  | 'k' => some 0
  | _ => none

/-- The node for a symbol applied to its (already parsed) arguments. -/
def mkNode : Char → List E → Option E
  | '0', [] => some .zero
  | 'i', [] => some .i
  | 'j', [] => some .j
  | 'k', [] => some .k
  | 'a', [x] => some (.a x)
  | 'b', [x] => some (.b x)
  | 'c', [x, y] => some (.c x y)
  | 'd', [x, y, z] => some (.d x y z)
  | 'f', args => some (.self args)
  | ch, args => if (baseArity ch).isNone then some (.call ch args) else none

/-- One step of the stack parser (the top of the stack is the head of the list). -/
def parseStep (arity : Char → Option ℕ) (farity : ℕ) (st : Option (List E)) (ch : Char) :
    Option (List E) :=
  match st with
  | none => none
  | some st =>
    match (if ch = 'f' then some farity else arity ch) with
    | none => none
    | some n =>
      if n ≤ st.length then
        match mkNode ch (st.take n).reverse with
        | some node => some (node :: st.drop n)
        | none => none
      else none

/-- Parse a postfix program string into its expression tree. -/
def parse (arity : Char → Option ℕ) (farity : ℕ) (s : String) : Option E :=
  match s.toList.foldl (parseStep arity farity) (some []) with
  | some [e] => some e
  | _ => none

/-- The arity of a program text: the highest of `i j k` it uses. -/
def textArity (s : String) : ℕ :=
  s.toList.foldl (fun m ch => max m (if ch = 'i' then 1 else if ch = 'j' then 2 else
    if ch = 'k' then 3 else 0)) 0

/-! ## The programs

First the strings exactly as on the website (Table 1 and the integer and rational programs of
`programs.py`), then the expression trees the theorems are about; `table_parses` checks that
they agree. -/

/-- The table of programs: symbol and program string. -/
def table : List (Char × String) := [
  -- Table 1: naturals and logic
  ('1', "00c"), ('2', "01c"), ('↑', "0ic"), ('-', "jibjbfid"), ('+', "iib0jcfjd"),
  ('*', "iibjfj+0d"), ('^', "jijbfi*1d"), ('!', "iiibf*1d"), ('¬', "i01d"), ('&', "ij10d0d"),
  ('∨', "i1j10dd"), ('<', "jiibjbf1d0d"), ('%', "ij<iij-jfd"), ('Δ', "ij%¬"),
  ('P', "jbijΔ¬ijbf&1d"), ('Π', "iibP"),
  -- further naturals programs of programs.py
  ('E', "iibf¬1d"), ('≤', "ji<¬"), ('|', "jiΔ"), ('~', "iEjEe"),
  ('G', "jjij%fid"), ('Q', "ij<00ij-jfcd"),
  -- integers as pairs {a, b} standing for a - b
  ('N', "ibiac"), ('A', "iaja+ibjb+c"), ('S', "iajb+ibja+c"), ('M', "iaja*ibjb*+iajb*ibja*+c"),
  ('R', "iaib<0ibia-ciaib-0cd"), ('L', "jaib+iajb+<¬"), ('V', "iaib+jajb+iaib+Δjajb+01dd"),
  ('⊞', "ijAR"), ('⊟', "ijSR"), ('⊠', "ijMR"),
  -- rationals as pairs {canonical integer, natural ≥ 1} in lowest terms
  ('⊙', "ij0cM"), ('g', "iaaiab+ibG"), ('Y', "iaaigQiabigQcibigQc"),
  ('⊕', "iajb⊙jaib⊙ARibjb*cY"), ('⊖', "iajb⊙jaib⊙SRibjb*cY"), ('⊗', "iajaMibjb*cY"),
  ('⊘', "jabiajb⊙Niajb⊙dibjaajab+*cY"), ('⊝', "iaNibc"), ('≼', "iajb⊙jaib⊙L"),
  -- binary naturals: lists of bits, least significant first, without trailing zeros
  ('s', "iia0ibfc1ibcd10cd"), ('p', "ijiaja0ibjbfsc1ibjbfcdja1ibjbfc0ibjbfcddidjd"),
  ('w', "i0icid"), ('m', "iiajibjfwpibjfwd0d"), ('β', "iibfs0d"), ('ν', "iibfibf+ia+0d"),
  -- equality as an ordinary program (with `a b d f` and the numeral `1` only)
  ('e', "ijiajafibjbf0d0dj01dd"),
  -- the meta-circular evaluator: list index, chain of `c`-nodes, interpreter
  ('u', "iibjbfjad"), ('λ', "i00c0iaibf0cccc00cd"),
  ('ε', "iaiabiabbiabbbiabbbbiabbbbbibakuibbλjkfkfibbajkfibbbajkfibbbbajkfddibbajkfbdibbajkfadibajudibbajkfibbbajkfcd0d")]

/-- The arity of every symbol: base symbols by their fixed arities, defined symbols by the
`i j k` used in their program. -/
def arity (ch : Char) : Option ℕ :=
  match baseArity ch with
  | some n => some n
  | none => (table.lookup ch).map textArity

/-- Parse the program of a symbol of the table. -/
def parseTable (ch : Char) : Option E :=
  (table.lookup ch).bind fun s => parse arity (textArity s) s

open E in
/-- The expression trees of the programs of the table (checked against the strings by
`table_parses`). -/
def defs : Char → Option E
  | '1' => some (c zero zero)                                           -- 00c
  | '2' => some (c zero (call '1' []))                                  -- 01c
  | '↑' => some (c zero i)                                              -- 0ic
  | '-' => some (d j (self [b i, b j]) i)                               -- jibjbfid
  | '+' => some (d i (self [b i, c zero j]) j)                          -- iib0jcfjd
  | '*' => some (d i (call '+' [self [b i, j], j]) zero)                -- iibjfj+0d
  | '^' => some (d j (call '*' [self [i, b j], i]) (call '1' []))       -- jijbfi*1d
  | '!' => some (d i (call '*' [i, self [b i]]) (call '1' []))          -- iiibf*1d
  | '¬' => some (d i zero (call '1' []))                                -- i01d
  | '&' => some (d i (d j (call '1' []) zero) zero)                     -- ij10d0d
  | '∨' => some (d i (call '1' []) (d j (call '1' []) zero))            -- i1j10dd
  | '<' => some (d j (d i (self [b i, b j]) (call '1' [])) zero)        -- jiibjbf1d0d
  | '%' => some (d (call '<' [i, j]) i (self [call '-' [i, j], j]))     -- ij<iij-jfd
  | 'Δ' => some (call '¬' [call '%' [i, j]])                            -- ij%¬
  | 'P' => some (d (b j) (call '&' [call '¬' [call 'Δ' [i, j]], self [i, b j]]) (call '1' []))
                                                                        -- jbijΔ¬ijbf&1d
  | 'Π' => some (call 'P' [i, b i])                                     -- iibP
  | 'E' => some (d i (call '¬' [self [b i]]) (call '1' []))             -- iibf¬1d
  | '≤' => some (call '¬' [call '<' [j, i]])                            -- ji<¬
  | '|' => some (call 'Δ' [j, i])                                       -- jiΔ
  | '~' => some (call 'e' [call 'E' [i], call 'E' [j]])                 -- iEjEe
  | 'G' => some (d j (self [j, call '%' [i, j]]) i)                     -- jjij%fid
  | 'Q' => some (d (call '<' [i, j]) zero (c zero (self [call '-' [i, j], j])))
                                                                        -- ij<00ij-jfcd
  | 'N' => some (c (b i) (a i))                                         -- ibiac
  | 'A' => some (c (call '+' [a i, a j]) (call '+' [b i, b j]))         -- iaja+ibjb+c
  | 'S' => some (c (call '+' [a i, b j]) (call '+' [b i, a j]))         -- iajb+ibja+c
  | 'M' => some (c (call '+' [call '*' [a i, a j], call '*' [b i, b j]])
                  (call '+' [call '*' [a i, b j], call '*' [b i, a j]]))
                                                                        -- iaja*ibjb*+iajb*ibja*+c
  | 'R' => some (d (call '<' [a i, b i]) (c zero (call '-' [b i, a i]))
                  (c (call '-' [a i, b i]) zero))                       -- iaib<0ibia-ciaib-0cd
  | 'L' => some (call '¬' [call '<' [call '+' [a j, b i], call '+' [a i, b j]]])
                                                                        -- jaib+iajb+<¬
  | 'V' => some (d (call '+' [a i, b i]) (call 'Δ' [call '+' [a j, b j], call '+' [a i, b i]])
                  (d (call '+' [a j, b j]) zero (call '1' [])))
                                                                        -- iaib+jajb+iaib+Δjajb+01dd
  | '⊞' => some (call 'R' [call 'A' [i, j]])                            -- ijAR
  | '⊟' => some (call 'R' [call 'S' [i, j]])                            -- ijSR
  | '⊠' => some (call 'R' [call 'M' [i, j]])                            -- ijMR
  | '⊙' => some (call 'M' [i, c j zero])                                -- ij0cM
  | 'g' => some (call 'G' [call '+' [a (a i), b (a i)], b i])           -- iaaiab+ibG
  | 'Y' => some (c (c (call 'Q' [a (a i), call 'g' [i]]) (call 'Q' [b (a i), call 'g' [i]]))
                  (call 'Q' [b i, call 'g' [i]]))                       -- iaaigQiabigQcibigQc
  | '⊕' => some (call 'Y' [c (call 'R' [call 'A' [call '⊙' [a i, b j], call '⊙' [a j, b i]]])
                  (call '*' [b i, b j])])                               -- iajb⊙jaib⊙ARibjb*cY
  | '⊖' => some (call 'Y' [c (call 'R' [call 'S' [call '⊙' [a i, b j], call '⊙' [a j, b i]]])
                  (call '*' [b i, b j])])                               -- iajb⊙jaib⊙SRibjb*cY
  | '⊗' => some (call 'Y' [c (call 'M' [a i, a j]) (call '*' [b i, b j])])
                                                                        -- iajaMibjb*cY
  | '⊘' => some (call 'Y' [c (d (b (a j)) (call 'N' [call '⊙' [a i, b j]]) (call '⊙' [a i, b j]))
                  (call '*' [b i, call '+' [a (a j), b (a j)]])])
                                                                        -- jabiajb⊙Niajb⊙dibjaajab+*cY
  | '⊝' => some (c (call 'N' [a i]) (b i))                              -- iaNibc
  | '≼' => some (call 'L' [call '⊙' [a i, b j], call '⊙' [a j, b i]])  -- iajb⊙jaib⊙L
  | 's' => some (d i (d (a i) (c zero (self [b i])) (c (call '1' []) (b i))) (c (call '1' []) zero))
                                                                        -- iia0ibfc1ibcd10cd
  | 'p' => some (d i (d j (d (a i)
                  (d (a j) (c zero (call 's' [self [b i, b j]])) (c (call '1' []) (self [b i, b j])))
                  (d (a j) (c (call '1' []) (self [b i, b j])) (c zero (self [b i, b j])))) i) j)
                                                  -- ijiaja0ibjbfsc1ibjbfcdja1ibjbfc0ibjbfcddidjd
  | 'w' => some (d i (c zero i) i)                                      -- i0icid
  | 'm' => some (d i (d (a i) (call 'p' [j, call 'w' [self [b i, j]]]) (call 'w' [self [b i, j]]))
                  zero)                                                 -- iiajibjfwpibjfwd0d
  | 'β' => some (d i (call 's' [self [b i]]) zero)                      -- iibfs0d
  | 'ν' => some (d i (call '+' [call '+' [self [b i], self [b i]], a i]) zero)
                                                                        -- iibfibf+ia+0d
  | 'e' => some (d i (d j (d (self [a i, a j]) (self [b i, b j]) zero) zero)
                  (d j zero (call '1' [])))                             -- ijiajafibjbf0d0dj01dd
  | 'u' => some (d i (self [b i, b j]) (a j))                            -- iibjbfjad
  | 'λ' => some (d i (c (c zero zero) (c zero (c (a i) (c (self [b i]) zero)))) (c zero zero))
                                                                        -- i00c0iaibf0cccc00cd
  | 'ε' => some (d (a i) (d (b (a i)) (d (b (b (a i))) (d (b (b (b (a i))))
                  (d (b (b (b (b (a i))))) (d (b (b (b (b (b (a i))))))
                    (self [call 'u' [a (b i), k], self [call 'λ' [b (b i)], j, k], k])
                    (d (self [a (b (b i)), j, k]) (self [a (b (b (b i))), j, k])
                      (self [a (b (b (b (b i)))), j, k])))
                  (b (self [a (b (b i)), j, k])))
                  (a (self [a (b (b i)), j, k])))
                  (call 'u' [a (b i), j]))
                  (c (self [a (b (b i)), j, k]) (self [a (b (b (b i))), j, k])))
                  zero)
    -- iaiabiabbiabbbiabbbbiabbbbbibakuibbλjkfkfibbajkfibbbajkfibbbbajkfddibbajkfbd
    -- ibbajkfadibajudibbajkfibbbajkfcd0d
  | _ => none

set_option maxRecDepth 4000 in
/-- Every program string of the table parses to the expression tree in `defs` (checked by
evaluating the parser inside the kernel: `rfl`). -/
theorem table_parses : ∀ p ∈ table, parseTable p.1 = defs p.1 :=
  List.map_eq_map_iff.mp (rfl : table.map (fun p => parseTable p.1) = table.map (fun p => defs p.1))

/-- The expression tree of `+` = `iib0jcfjd` as printed in the paper (with `0jc`, the successor of
`j` written inline, instead of a call `j↑`); it is the tree `defs '+'` of the table. -/
def plusPaper : E := .d .i (.self [.b .i, .c .zero .j]) .j

theorem plusPaper_parses : parse arity 2 "iib0jcfjd" = some plusPaper := rfl

/-! ## Running programs -/

/-- `Computes c args v`: calling the defined symbol `c` on the arguments `args` yields `v`. -/
def Computes (c : Char) (args : List V) (v : V) : Prop :=
  ∃ e, defs c = some e ∧ Eval defs e args e v

theorem Computes.det {c : Char} {args : List V} {v w : V} (h₁ : Computes c args v)
    (h₂ : Computes c args w) : v = w := by
  obtain ⟨e, he, h₁⟩ := h₁
  obtain ⟨e', he', h₂⟩ := h₂
  cases Option.some.inj (he.symm.trans he')
  exact Eval.det h₁ h₂

/-- A call of a defined symbol, given the evaluation of the arguments and of the callee. -/
theorem Eval.callOf {body : E} {env : List V} {c : Char} {xs : List E} {vs : List V} {v : V}
    (hargs : EvalList defs body env xs vs) (h : Computes c vs v) :
    Eval defs body env (.call c xs) v :=
  match h with
  | ⟨_, he, hv⟩ => .call he hargs hv

/-- Executable: call the symbol `c` on `args` with the given fuel. -/
def run (fuel : ℕ) (c : Char) (args : List V) : Option V :=
  match defs c with
  | some e => evalF defs fuel e args e
  | none => none

theorem Computes.of_run {fuel : ℕ} {c : Char} {args : List V} {v : V}
    (h : run fuel c args = some v) : Computes c args v := by
  unfold run at h
  split at h
  · rename_i e he; exact ⟨e, he, evalF_sound h⟩
  · exact absurd h (by simp)

/-- Sanity checks of the executable evaluator. -/
example : run 50 '+' [num 2, num 3] = some (num 5) := by decide
example : run 50 '*' [num 3, num 4] = some (num 12) := by decide
example : run 50 '^' [num 2, num 3] = some (num 8) := by decide
example : run 50 '!' [num 4] = some (num 24) := by decide
example : run 50 '-' [num 1, num 2] = none := by decide   -- `b` of `0`: undefined
example : run 50 'Π' [num 7] = some (num 1) := by decide
example : run 50 'Π' [num 9] = some (num 0) := by decide
example : run 50 'Π' [num 0] = none := by decide           -- `Π` is undefined at 0 and 1
example : run 50 'Π' [num 1] = none := by decide
example : run 50 'Δ' [num 3, num 0] = none := by decide    -- `Δ(i, 0)` does not terminate
example : run 50 'Δ' [num 6, num 3] = some (num 1) := by decide
example : run 50 'Δ' [num 7, num 3] = some (num 0) := by decide
example : run 50 'Q' [num 7, num 2] = some (num 3) := by decide

#eval (run 1000 '!' [num 5]).map val
#eval ((List.range 20).filter fun n => run 200 'Π' [num n] = some (num 1))

/-! ## Table 1: the naturals and logic programs compute what they claim -/

theorem one_computes : Computes '1' [] (num 1) := ⟨_, rfl, .c .zero .zero⟩

theorem two_computes : Computes '2' [] (num 2) := ⟨_, rfl, .c .zero (.callOf .nil one_computes)⟩

/-- `↑` = `0ic` is the successor. -/
theorem succ_computes (n : ℕ) : Computes '↑' [num n] (num (n + 1)) := ⟨_, rfl, .c .zero .i⟩

/-- `-` = `jibjbfid` computes `m - n` when `n ≤ m`. -/
theorem sub_computes (m n : ℕ) (h : n ≤ m) : Computes '-' [num m, num n] (num (m - n)) := by
  refine ⟨_, rfl, ?_⟩
  induction n generalizing m with
  | zero => rw [Nat.sub_zero]; exact .dF .j .i
  | succ n ih =>
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [Nat.add_sub_add_right]
    exact .dT .j (.self (.two (.b .i) (.b .j)) (ih m (by omega)))

/-- `+` = `iib0jcfjd` computes `m + n`: if `m` then `(m - 1) + {0, n}` else `n`. -/
theorem plus_computes (m n : ℕ) : Computes '+' [num m, num n] (num (m + n)) := by
  refine ⟨_, rfl, ?_⟩
  induction m generalizing n with
  | zero => rw [Nat.zero_add]; exact .dF .i .j
  | succ m ih =>
    rw [show m + 1 + n = m + (n + 1) by omega]
    exact .dT .i (.self (.two (.b .i) (.c .zero .j)) (ih (n + 1)))

/-- The same, stated for the expression tree `plusPaper` (which is `defs '+'`). -/
theorem plusPaper_computes (m n : ℕ) :
    Eval defs plusPaper [num m, num n] plusPaper (num (m + n)) := by
  induction m generalizing n with
  | zero => rw [Nat.zero_add]; exact .dF .i .j
  | succ m ih =>
    rw [show m + 1 + n = m + (n + 1) by omega]
    exact .dT .i (.self (.two (.b .i) (.c .zero .j)) (ih (n + 1)))

/-- `*` = `iibjfj+0d` computes `m * n`. -/
theorem times_computes (m n : ℕ) : Computes '*' [num m, num n] (num (m * n)) := by
  refine ⟨_, rfl, ?_⟩
  induction m with
  | zero => rw [Nat.zero_mul]; exact .dF .i .zero
  | succ m ih =>
    rw [Nat.succ_mul]
    exact .dT .i (.callOf (.two (.self (.two (.b .i) .j) ih) .j) (plus_computes (m * n) n))

/-- `^` = `jijbfi*1d` computes `m ^ n`. -/
theorem pow_computes (m n : ℕ) : Computes '^' [num m, num n] (num (m ^ n)) := by
  refine ⟨_, rfl, ?_⟩
  induction n with
  | zero => rw [Nat.pow_zero]; exact .dF .j (.callOf .nil one_computes)
  | succ n ih =>
    rw [Nat.pow_succ]
    exact .dT .j (.callOf (.two (.self (.two .i (.b .j)) ih) .i) (times_computes (m ^ n) m))

/-- `!` = `iiibf*1d` computes `n!`. -/
theorem fact_computes (n : ℕ) : Computes '!' [num n] (num n.factorial) := by
  refine ⟨_, rfl, ?_⟩
  induction n with
  | zero => rw [Nat.factorial_zero]; exact .dF .i (.callOf .nil one_computes)
  | succ n ih =>
    rw [Nat.factorial_succ]
    exact .dT .i (.callOf (.two .i (.self (.one (.b .i)) ih)) (times_computes (n + 1) n.factorial))

/-- `¬` = `i01d` is negation on Booleans. -/
theorem not_computes (p : Bool) : Computes '¬' [boolV p] (boolV (!p)) := by
  cases p <;> exact .of_run (fuel := 10) (by decide)

/-- `&` = `ij10d0d` is conjunction on Booleans. -/
theorem and_computes (p q : Bool) : Computes '&' [boolV p, boolV q] (boolV (p && q)) := by
  cases p <;> cases q <;> exact .of_run (fuel := 10) (by decide)

/-- `∨` = `i1j10dd` is disjunction on Booleans. -/
theorem or_computes (p q : Bool) : Computes '∨' [boolV p, boolV q] (boolV (p || q)) := by
  cases p <;> cases q <;> exact .of_run (fuel := 10) (by decide)

/-- `<` = `jiibjbf1d0d` computes the Boolean of `m < n`. -/
theorem lt_computes (m n : ℕ) : Computes '<' [num m, num n] (boolV (decide (m < n))) := by
  refine ⟨_, rfl, ?_⟩
  induction n generalizing m with
  | zero =>
    rw [decide_eq_false (Nat.not_lt_zero m)]
    exact .dF .j .zero
  | succ n ih =>
    cases m with
    | zero =>
      rw [decide_eq_true (Nat.succ_pos n)]
      exact .dT .j (.dF .i (.callOf .nil one_computes))
    | succ m =>
      rw [boolV_congr (Nat.add_lt_add_iff_right (k := 1))]
      exact .dT .j (.dT .i (.self (.two (.b .i) (.b .j)) (ih m)))

/-- `¬` on a numeral: `1` if it is `0`, `0` otherwise (every pair counts as true). -/
theorem not_num_computes (n : ℕ) : Computes '¬' [num n] (boolV (decide (n = 0))) := by
  cases n with
  | zero => exact ⟨_, rfl, .dF .i (.callOf .nil one_computes)⟩
  | succ n => exact ⟨_, rfl, .dT .i .zero⟩

/-- `%` = `ij<iij-jfd` computes `i % j`, for `j ≥ 1`. -/
theorem mod_computes (i j : ℕ) (hj : 1 ≤ j) : Computes '%' [num i, num j] (num (i % j)) := by
  refine ⟨_, rfl, ?_⟩
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  have hl := lt_computes i j
  by_cases h : i < j
  · rw [decide_eq_true h] at hl
    rw [Nat.mod_eq_of_lt h]
    exact .dT (.callOf (.two .i .j) hl) .i
  · rw [decide_eq_false h] at hl
    rw [Nat.mod_eq_sub_mod (by omega)]
    exact .dF (.callOf (.two .i .j) hl)
      (.self (.two (.callOf (.two .i .j) (sub_computes i j (by omega))) .j) (ih (i - j) (by omega)))

/-- `Δ` = `ij%¬` computes the Boolean of `j ∣ i`, for `j ≥ 1`: `¬ (i % j)`. -/
theorem dvd_computes (i j : ℕ) (hj : 1 ≤ j) : Computes 'Δ' [num i, num j] (boolV (decide (j ∣ i))) := by
  rw [boolV_congr (Nat.dvd_iff_mod_eq_zero ..)]
  exact ⟨_, rfl, .callOf (.one (.callOf (.two .i .j) (mod_computes i j hj))) (not_num_computes _)⟩

/-- "`i` is indivisible by all of `2 .. j`", the meaning of `P` (the decidability instance is
given by hand because instance search does not find `Nat.decidableLoHiLe` here). -/
def noDivisorUpTo (i j : ℕ) : Bool :=
  @decide (∀ d, 2 ≤ d → d ≤ j → ¬ d ∣ i) (Nat.decidableLoHiLe 2 j _)

theorem noDivisorUpTo_one (i : ℕ) : noDivisorUpTo i 1 = true := by
  unfold noDivisorUpTo
  exact decide_eq_true fun _ h1 h2 => by omega

theorem noDivisorUpTo_succ (i j : ℕ) :
    noDivisorUpTo i (j + 2) = (!decide (j + 2 ∣ i) && noDivisorUpTo i (j + 1)) := by
  unfold noDivisorUpTo
  rw [← decide_not, ← Bool.decide_and, decide_eq_decide]
  constructor
  · intro h; exact ⟨h _ (by omega) le_rfl, fun d h1 h2 => h d h1 (by omega)⟩
  · rintro ⟨h1, h2⟩ d hd1 hd2
    rcases Nat.lt_or_ge d (j + 2) with hlt | hge
    · exact h2 d hd1 (by omega)
    · obtain rfl : d = j + 2 := by omega
      exact h1

/-- `P` = `jbijΔ¬ijbf&1d` computes the Boolean of "no `d` with `2 ≤ d ≤ j` divides `i`",
for `j ≥ 1`. -/
theorem P_computes (i j : ℕ) (hj : 1 ≤ j) : Computes 'P' [num i, num j] (boolV (noDivisorUpTo i j)) := by
  refine ⟨_, rfl, ?_⟩
  induction j with
  | zero => omega
  | succ j ih =>
    cases j with
    | zero =>
      rw [noDivisorUpTo_one]
      exact .dF (.b .j) (.callOf .nil one_computes)
    | succ j =>
      rw [noDivisorUpTo_succ]
      exact .dT (.b .j) (.callOf (.two
        (.callOf (.one (.callOf (.two .i .j) (dvd_computes i (j + 2) (by omega)))) (not_computes _))
        (.self (.two .i (.b .j)) (ih (by omega)))) (and_computes _ _))

/-- `Π` = `iibP` computes the Boolean of `Nat.Prime n`, for `n ≥ 2`. -/
theorem prime_computes (n : ℕ) (hn : 2 ≤ n) : Computes 'Π' [num n] (boolV (decide (Nat.Prime n))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have key : Nat.Prime (m + 1) ↔ ∀ d, 2 ≤ d → d ≤ m → ¬ d ∣ m + 1 := by
    rw [Nat.prime_def_lt']
    constructor
    · rintro ⟨-, h⟩ d h1 h2; exact h d h1 (by omega)
    · intro h; exact ⟨hn, fun d h1 h2 => h d h1 (by omega)⟩
  rw [@boolV_congr _ _ _ (Nat.decidableLoHiLe 2 m _) key]
  exact ⟨_, rfl, .callOf (.two .i (.b .i)) (P_computes (m + 1) m (by omega))⟩

/-- For `n ≥ 2`: `Π` returns `1` on `n` if and only if `n` is prime (and otherwise it returns
`0`, by `prime_computes` and determinism). -/
theorem prime_iff (n : ℕ) (hn : 2 ≤ n) : Computes 'Π' [num n] (num 1) ↔ Nat.Prime n := by
  constructor
  · intro h
    have h' := Computes.det h (prime_computes n hn)
    by_contra hp
    rw [decide_eq_false hp] at h'
    exact absurd h' (by decide)
  · intro hp
    have h := prime_computes n hn
    rwa [decide_eq_true hp] at h

/-! ### The other naturals programs of `programs.py` -/

/-- `E` = `iibf¬1d` computes the Boolean of "`n` is even". -/
theorem even_computes (n : ℕ) : Computes 'E' [num n] (boolV (decide (n % 2 = 0))) := by
  refine ⟨_, rfl, ?_⟩
  induction n with
  | zero =>
    rw [decide_eq_true (by omega : 0 % 2 = 0)]
    exact .dF .i (.callOf .nil one_computes)
  | succ n ih =>
    rw [boolV_congr (show (n + 1) % 2 = 0 ↔ ¬ (n % 2 = 0) by omega), decide_not]
    exact .dT .i (.callOf (.one (.self (.one (.b .i)) ih)) (not_computes _))

/-- `≤` = `ji<¬` computes the Boolean of `m ≤ n`. -/
theorem le_computes (m n : ℕ) : Computes '≤' [num m, num n] (boolV (decide (m ≤ n))) := by
  rw [boolV_congr (show m ≤ n ↔ ¬ (n < m) by omega), decide_not]
  exact ⟨_, rfl, .callOf (.one (.callOf (.two .j .i) (lt_computes n m))) (not_computes _)⟩

/-- `|` = `jiΔ` computes the Boolean of `m ∣ n`, for `m ≥ 1`. -/
theorem divides_computes (m n : ℕ) (hm : 1 ≤ m) :
    Computes '|' [num m, num n] (boolV (decide (m ∣ n))) :=
  ⟨_, rfl, .callOf (.two .j .i) (dvd_computes n m hm)⟩

/-! ### Equality

Equality is not a primitive of the language: `e` is the program `ijiajafibjbf0d0dj01dd` of the
table, written with `a b d f` and the numeral `1` only. -/

theorem Computes.eval {c : Char} {e : E} {args : List V} {v : V} (h : Computes c args v)
    (hc : defs c = some e) : Eval defs e args e v := by
  obtain ⟨e', he', h⟩ := h
  cases Option.some.inj (hc.symm.trans he')
  exact h

/-- The tree of the program `e` = `ijiajafibjbf0d0dj01dd`: `if i (if j (if f(a i, a j) f(b i, b j) 0)
0) (if j 0 1)`, where `f` is `e` itself. -/
def eqBody : E :=
  .d .i (.d .j (.d (.self [.a .i, .a .j]) (.self [.b .i, .b .j]) .zero) .zero)
    (.d .j .zero (.call '1' []))

theorem defs_e : defs 'e' = some eqBody := rfl

/-- The program `e` computes equality: `1` if the two values are equal, `0` otherwise. -/
theorem eq_computes (x y : V) : Computes 'e' [x, y] (if x = y then num 1 else .atom) := by
  induction x generalizing y with
  | atom =>
    cases y with
    | atom => exact ⟨_, rfl, .dF .i (.dF .j (.callOf .nil one_computes))⟩
    | pair u w => exact ⟨_, rfl, .dF .i (.dT .j .zero)⟩
  | pair u w ihu ihw =>
    cases y with
    | atom => exact ⟨_, rfl, .dT .i (.dF .j .zero)⟩
    | pair u' w' =>
      by_cases hu : u = u'
      · subst hu
        have h1 := (ihu u).eval rfl
        rw [ite_eq_left rfl] at h1
        rw [show (if V.pair u w = V.pair u w' then num 1 else V.atom) =
          (if w = w' then num 1 else V.atom) by simp]
        exact ⟨_, rfl, .dT .i (.dT .j (.dT (.self (.two (.a .i) (.a .j)) h1)
          (.self (.two (.b .i) (.b .j)) ((ihw w').eval rfl))))⟩
      · have h1 := (ihu u').eval rfl
        rw [ite_eq_right hu] at h1
        rw [ite_eq_right (by simp [hu])]
        exact ⟨_, rfl, .dT .i (.dT .j (.dF (.self (.two (.a .i) (.a .j)) h1) .zero))⟩

/-- `~` = `iEjEe` computes the Boolean of "`m` and `n` have the same parity" (by calling the
program `e` on the two parities). -/
theorem parity_computes (m n : ℕ) : Computes '~' [num m, num n] (boolV (decide (m % 2 = n % 2))) := by
  have key : boolV (decide (m % 2 = n % 2)) =
      (if boolV (decide (m % 2 = 0)) = boolV (decide (n % 2 = 0)) then num 1 else .atom) := by
    rcases Nat.mod_two_eq_zero_or_one m with hm | hm <;>
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;> simp [hm, hn, boolV]
  rw [key]
  exact ⟨_, rfl, .callOf (.two (.callOf (.one .i) (even_computes m))
    (.callOf (.one .j) (even_computes n))) (eq_computes _ _)⟩

/-- `G` = `jjij%fid` computes `gcd i j`. -/
theorem gcd_computes (i j : ℕ) : Computes 'G' [num i, num j] (num (Nat.gcd i j)) := by
  refine ⟨_, rfl, ?_⟩
  induction j using Nat.strong_induction_on generalizing i with
  | _ j ih =>
  cases j with
  | zero => rw [Nat.gcd_zero_right]; exact .dF .j .i
  | succ j =>
    rw [Nat.gcd_comm, Nat.gcd_rec, Nat.gcd_comm]
    exact .dT .j (.self (.two .j (.callOf (.two .i .j) (mod_computes i (j + 1) (by omega))))
      (ih (i % (j + 1)) (Nat.mod_lt _ (by omega)) (j + 1)))

/-- `Q` = `ij<00ij-jfcd` computes `i / j` (the quotient), for `j ≥ 1`: if `i < j` then `0` else
`{0, Q(i - j, j)}`. -/
theorem quot_computes (i j : ℕ) (hj : 1 ≤ j) : Computes 'Q' [num i, num j] (num (i / j)) := by
  refine ⟨_, rfl, ?_⟩
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  have hl := lt_computes i j
  by_cases h : i < j
  · rw [decide_eq_true h] at hl
    rw [Nat.div_eq_of_lt h]
    exact .dT (.callOf (.two .i .j) hl) .zero
  · rw [decide_eq_false h] at hl
    rw [Nat.div_eq_sub_div (by omega) (by omega)]
    exact .dF (.callOf (.two .i .j) hl) (.c .zero (.self (.two (.callOf (.two .i .j)
      (sub_computes i j (by omega))) .j) (ih (i - j) (by omega))))

/-! ## Integers as pairs `{a, b}` standing for `a - b` -/

/-- The integer represented by a pair of naturals `{num a, num b}`: `a - b`. -/
def zval : V → ℤ
  | .pair x y => (val x : ℤ) - val y
  | .atom => 0

/-- The canonical pair of an integer: `{num k, 0}` for `k ≥ 0` and `{0, num (-k)}` for `k < 0`. -/
def zpair (k : ℤ) : V := .pair (num k.toNat) (num (-k).toNat)

@[simp] theorem zval_zpair (k : ℤ) : zval (zpair k) = k := by
  simp only [zval, zpair, val_num]; omega

theorem zpair_of_le {a b : ℕ} (h : b ≤ a) : zpair ((a : ℤ) - b) = .pair (num (a - b)) .atom := by
  simp only [zpair, show ((a : ℤ) - b).toNat = a - b by omega,
    show (-((a : ℤ) - b)).toNat = 0 by omega, num_zero]

theorem zpair_of_lt {a b : ℕ} (h : a < b) : zpair ((a : ℤ) - b) = .pair .atom (num (b - a)) := by
  simp only [zpair, show ((a : ℤ) - b).toNat = 0 by omega,
    show (-((a : ℤ) - b)).toNat = b - a by omega, num_zero]

/-- `N` = `ibiac` negates an integer by swapping the parts. -/
theorem neg_computes (u w : V) : Computes 'N' [.pair u w] (.pair w u) :=
  ⟨_, rfl, .c (.b .i) (.a .i)⟩

/-- `A` = `iaja+ibjb+c` adds integers partwise: `{a,b} + {c,d} = {a+c, b+d}`. -/
theorem A_computes (a b c d : ℕ) :
    Computes 'A' [.pair (num a) (num b), .pair (num c) (num d)] (.pair (num (a + c)) (num (b + d))) :=
  ⟨_, rfl, .c (.callOf (.two (.a .i) (.a .j)) (plus_computes a c))
    (.callOf (.two (.b .i) (.b .j)) (plus_computes b d))⟩

/-- `S` = `iajb+ibja+c` subtracts integers: `{a,b} - {c,d} = {a+d, b+c}`. -/
theorem S_computes (a b c d : ℕ) :
    Computes 'S' [.pair (num a) (num b), .pair (num c) (num d)] (.pair (num (a + d)) (num (b + c))) :=
  ⟨_, rfl, .c (.callOf (.two (.a .i) (.b .j)) (plus_computes a d))
    (.callOf (.two (.b .i) (.a .j)) (plus_computes b c))⟩

/-- `M` = `iaja*ibjb*+iajb*ibja*+c` multiplies integers: `{a,b} * {c,d} = {ac+bd, ad+bc}`. -/
theorem M_computes (a b c d : ℕ) :
    Computes 'M' [.pair (num a) (num b), .pair (num c) (num d)]
      (.pair (num (a * c + b * d)) (num (a * d + b * c))) :=
  ⟨_, rfl, .c
    (.callOf (.two (.callOf (.two (.a .i) (.a .j)) (times_computes a c))
      (.callOf (.two (.b .i) (.b .j)) (times_computes b d))) (plus_computes _ _))
    (.callOf (.two (.callOf (.two (.a .i) (.b .j)) (times_computes a d))
      (.callOf (.two (.b .i) (.a .j)) (times_computes b c))) (plus_computes _ _))⟩

/-- `R` = `iaib<0ibia-ciaib-0cd` reduces a pair to the canonical pair of the same integer. -/
theorem R_computes (a b : ℕ) : Computes 'R' [.pair (num a) (num b)] (zpair ((a : ℤ) - b)) := by
  refine ⟨_, rfl, ?_⟩
  have hl := lt_computes a b
  by_cases h : a < b
  · rw [decide_eq_true h] at hl
    rw [zpair_of_lt h]
    exact .dT (.callOf (.two (.a .i) (.b .i)) hl)
      (.c .zero (.callOf (.two (.b .i) (.a .i)) (sub_computes b a h.le)))
  · rw [decide_eq_false h] at hl
    rw [zpair_of_le (by omega)]
    exact .dF (.callOf (.two (.a .i) (.b .i)) hl)
      (.c (.callOf (.two (.a .i) (.b .i)) (sub_computes a b (by omega))) .zero)

/-- `L` = `jaib+iajb+<¬` computes the Boolean of `a - b ≤ c - d`. -/
theorem zle_computes (a b c d : ℕ) :
    Computes 'L' [.pair (num a) (num b), .pair (num c) (num d)]
      (boolV (decide ((a : ℤ) - b ≤ (c : ℤ) - d))) := by
  rw [boolV_congr (show ((a : ℤ) - b ≤ (c : ℤ) - d) ↔ ¬ (c + b < a + d) by omega), decide_not]
  exact ⟨_, rfl, .callOf (.one (.callOf (.two (.callOf (.two (.a .j) (.b .i)) (plus_computes c b))
    (.callOf (.two (.a .i) (.b .j)) (plus_computes a d))) (lt_computes (c + b) (a + d))))
    (not_computes _)⟩

/-- `⊞` = `ijAR` computes the canonical pair of the sum. -/
theorem zadd_computes (a b c d : ℕ) :
    Computes '⊞' [.pair (num a) (num b), .pair (num c) (num d)]
      (zpair (((a : ℤ) - b) + ((c : ℤ) - d))) := by
  rw [show ((a : ℤ) - b) + ((c : ℤ) - d) = ((a + c : ℕ) : ℤ) - ((b + d : ℕ) : ℤ) by push_cast; ring]
  exact ⟨_, rfl, .callOf (.one (.callOf (.two .i .j) (A_computes a b c d))) (R_computes _ _)⟩

/-- `⊟` = `ijSR` computes the canonical pair of the difference. -/
theorem zsub_computes (a b c d : ℕ) :
    Computes '⊟' [.pair (num a) (num b), .pair (num c) (num d)]
      (zpair (((a : ℤ) - b) - ((c : ℤ) - d))) := by
  rw [show ((a : ℤ) - b) - ((c : ℤ) - d) = ((a + d : ℕ) : ℤ) - ((b + c : ℕ) : ℤ) by push_cast; ring]
  exact ⟨_, rfl, .callOf (.one (.callOf (.two .i .j) (S_computes a b c d))) (R_computes _ _)⟩

/-- `⊠` = `ijMR` computes the canonical pair of the product. -/
theorem zmul_computes (a b c d : ℕ) :
    Computes '⊠' [.pair (num a) (num b), .pair (num c) (num d)]
      (zpair (((a : ℤ) - b) * ((c : ℤ) - d))) := by
  rw [show ((a : ℤ) - b) * ((c : ℤ) - d) =
    ((a * c + b * d : ℕ) : ℤ) - ((a * d + b * c : ℕ) : ℤ) by push_cast; ring]
  exact ⟨_, rfl, .callOf (.one (.callOf (.two .i .j) (M_computes a b c d))) (R_computes _ _)⟩

/-- `⊙` = `ij0cM` multiplies an integer pair by a natural. -/
theorem smul_computes (a b n : ℕ) :
    Computes '⊙' [.pair (num a) (num b), num n]
      (.pair (num (a * n + b * 0)) (num (a * 0 + b * n))) :=
  ⟨_, rfl, .callOf (.two .i (.c .j .zero)) (M_computes a b n 0)⟩

/-! The same on canonical inputs, stated with integers `x y : ℤ`. -/

theorem zadd_zpair (x y : ℤ) : Computes '⊞' [zpair x, zpair y] (zpair (x + y)) := by
  have h := zadd_computes x.toNat (-x).toNat y.toNat (-y).toNat
  rw [Int.toNat_sub_toNat_neg, Int.toNat_sub_toNat_neg] at h
  exact h

theorem zsub_zpair (x y : ℤ) : Computes '⊟' [zpair x, zpair y] (zpair (x - y)) := by
  have h := zsub_computes x.toNat (-x).toNat y.toNat (-y).toNat
  rw [Int.toNat_sub_toNat_neg, Int.toNat_sub_toNat_neg] at h
  exact h

theorem zmul_zpair (x y : ℤ) : Computes '⊠' [zpair x, zpair y] (zpair (x * y)) := by
  have h := zmul_computes x.toNat (-x).toNat y.toNat (-y).toNat
  rw [Int.toNat_sub_toNat_neg, Int.toNat_sub_toNat_neg] at h
  exact h

theorem zle_zpair (x y : ℤ) : Computes 'L' [zpair x, zpair y] (boolV (decide (x ≤ y))) := by
  have h := zle_computes x.toNat (-x).toNat y.toNat (-y).toNat
  rw [Int.toNat_sub_toNat_neg, Int.toNat_sub_toNat_neg] at h
  exact h

/-- The successor of an integer is `⊞` with `zpair 1 = {{0, 0}, 0}` (the program `i00c0c⊞` of
`programs.py`): `x + 1` on canonical pairs. -/
theorem zsucc_zpair (x : ℤ) : Computes '⊞' [zpair x, zpair 1] (zpair (x + 1)) :=
  zadd_zpair x 1

theorem zneg_zpair (x : ℤ) : Computes 'N' [zpair x] (zpair (-x)) := by
  have h := neg_computes (num x.toNat) (num (-x).toNat)
  rw [show zpair (-x) = .pair (num (-x).toNat) (num x.toNat) by simp [zpair]]
  exact h

/-! ## Rationals as pairs `{canonical integer, natural ≥ 1}` in lowest terms -/

/-- The value standing for the rational `r`: `{zpair r.num, num r.den}`. -/
def qpair (r : ℚ) : V := .pair (zpair r.num) (num r.den)

/-- `⊝` = `iaNibc` negates a rational. -/
theorem qneg_computes (r : ℚ) : Computes '⊝' [qpair r] (qpair (-r)) := by
  rw [show qpair (-r) = .pair (.pair (num (-r.num).toNat) (num r.num.toNat)) (num r.den) by
    simp [qpair, zpair]]
  exact ⟨_, rfl, .c (.callOf (.one (.a .i)) (neg_computes _ _)) (.b .i)⟩

theorem smul_cast (x : ℤ) (n : ℕ) :
    ((x.toNat * n + (-x).toNat * 0 : ℕ) : ℤ) - ((x.toNat * 0 + (-x).toNat * n : ℕ) : ℤ) = x * n := by
  rw [show x * n = ((x.toNat : ℤ) - (-x).toNat) * n by rw [Int.toNat_sub_toNat_neg]]
  push_cast; ring

/-- `≼` = `iajb⊙jaib⊙L` computes the Boolean of `r ≤ s` (cross-multiplication). -/
theorem qle_computes (r s : ℚ) : Computes '≼' [qpair r, qpair s] (boolV (decide (r ≤ s))) := by
  rw [boolV_congr (show r ≤ s ↔
      ((r.num.toNat * s.den + (-r.num).toNat * 0 : ℕ) : ℤ) -
          ((r.num.toNat * 0 + (-r.num).toNat * s.den : ℕ) : ℤ) ≤
        ((s.num.toNat * r.den + (-s.num).toNat * 0 : ℕ) : ℤ) -
          ((s.num.toNat * 0 + (-s.num).toNat * r.den : ℕ) : ℤ) by
    rw [smul_cast, smul_cast]; exact Rat.le_iff r s)]
  exact ⟨_, rfl, .callOf (.two (.callOf (.two (.a .i) (.b .j)) (smul_computes _ _ _))
    (.callOf (.two (.a .j) (.b .i)) (smul_computes _ _ _))) (zle_computes _ _ _ _)⟩


/-! ### `V`: integer divisibility, on canonical pairs

`V` reads `|x|` off a pair `{a, b}` as `a + b`, which is `|x|` only for canonical pairs (for
`{3, 3}` it gives 6, not 0); it is used on canonical pairs only, and that is what we prove. -/

/-- `V` = `iaib+jajb+iaib+Δjajb+01dd` computes the Boolean of `x ∣ y` on canonical pairs. -/
theorem zdvd_computes (x y : ℤ) : Computes 'V' [zpair x, zpair y] (boolV (decide (x ∣ y))) := by
  have hx := plus_computes x.toNat (-x).toNat
  have hy := plus_computes y.toNat (-y).toNat
  rw [Int.toNat_add_toNat_neg_eq_natAbs] at hx hy
  rcases Nat.eq_zero_or_pos x.natAbs with h0 | hpos
  · have hx0 : x = 0 := Int.natAbs_eq_zero.mp h0
    rw [h0] at hx
    rw [boolV_congr (show x ∣ y ↔ y.natAbs = 0 by rw [hx0, zero_dvd_iff, Int.natAbs_eq_zero])]
    rcases Nat.eq_zero_or_pos y.natAbs with hy0 | hypos
    · rw [hy0] at hy
      rw [decide_eq_true hy0]
      exact ⟨_, rfl, .dF (.callOf (.two (.a .i) (.b .i)) hx)
        (.dF (.callOf (.two (.a .j) (.b .j)) hy) (.callOf .nil one_computes))⟩
    · obtain ⟨k, hk⟩ : ∃ k, y.natAbs = k + 1 := ⟨y.natAbs - 1, by omega⟩
      rw [hk] at hy
      rw [decide_eq_false (by omega)]
      exact ⟨_, rfl, .dF (.callOf (.two (.a .i) (.b .i)) hx)
        (.dT (.callOf (.two (.a .j) (.b .j)) hy) .zero)⟩
  · obtain ⟨k, hk⟩ : ∃ k, x.natAbs = k + 1 := ⟨x.natAbs - 1, by omega⟩
    have hΔ := dvd_computes y.natAbs x.natAbs hpos
    rw [boolV_congr Int.natAbs_dvd_natAbs.symm]
    rw [hk] at hx hΔ ⊢
    exact ⟨_, rfl, .dT (.callOf (.two (.a .i) (.b .i)) hx)
      (.callOf (.two (.callOf (.two (.a .j) (.b .j)) hy) (.callOf (.two (.a .i) (.b .i)) hx)) hΔ)⟩

/-! ### Lowest terms: `g`, `Y`, and the four operations -/

/-- `g` = `iaaiab+ibG` computes `gcd (a + b) q` on `{{a, b}, q}` (`a + b = |p|` for canonical
`{a, b}`). -/
theorem g_computes (a b q : ℕ) :
    Computes 'g' [.pair (.pair (num a) (num b)) (num q)] (num (Nat.gcd (a + b) q)) :=
  ⟨_, rfl, .callOf (.two (.callOf (.two (.a (.a .i)) (.b (.a .i))) (plus_computes a b)) (.b .i))
    (gcd_computes _ _)⟩

/-- `Y` = `iaaigQiabigQcibigQc` divides the three parts by `g`. -/
theorem Y_computes (a b q : ℕ) (hq : 1 ≤ q) :
    Computes 'Y' [.pair (.pair (num a) (num b)) (num q)]
      (.pair (.pair (num (a / Nat.gcd (a + b) q)) (num (b / Nat.gcd (a + b) q)))
        (num (q / Nat.gcd (a + b) q))) := by
  have hg : 1 ≤ Nat.gcd (a + b) q := Nat.gcd_pos_of_pos_right _ hq
  exact ⟨_, rfl, .c
    (.c (.callOf (.two (.a (.a .i)) (.callOf (.one .i) (g_computes a b q))) (quot_computes a _ hg))
      (.callOf (.two (.b (.a .i)) (.callOf (.one .i) (g_computes a b q))) (quot_computes b _ hg)))
    (.callOf (.two (.b .i) (.callOf (.one .i) (g_computes a b q))) (quot_computes q _ hg))⟩

theorem zpair_neg (x : ℤ) : zpair (-x) = .pair (num (-x).toNat) (num x.toNat) := by
  simp [zpair]

/-- The canonical pair of a product, in terms of the parts of the factors (this is the shape
`M` produces on canonical inputs). -/
theorem zpair_mul (x y : ℤ) :
    zpair (x * y) = .pair (num (x.toNat * y.toNat + (-x).toNat * (-y).toNat))
      (num (x.toNat * (-y).toNat + (-x).toNat * y.toNat)) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg x <;> obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg y <;>
    simp only [Int.mul_neg, Int.neg_mul, Int.neg_neg, ← Int.natCast_mul, zpair, Int.toNat_natCast,
      Int.toNat_neg_natCast, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add]

theorem zpair_mul_natCast (x : ℤ) (n : ℕ) :
    zpair (x * n) = .pair (num (x.toNat * n + (-x).toNat * 0)) (num (x.toNat * 0 + (-x).toNat * n)) := by
  rw [zpair_mul]; simp only [Int.toNat_natCast, Int.toNat_neg_natCast]

theorem zpair_neg_mul_natCast (x : ℤ) (n : ℕ) :
    zpair (-(x * n)) =
      .pair (num (x.toNat * 0 + (-x).toNat * n)) (num (x.toNat * n + (-x).toNat * 0)) := by
  have h := zpair_mul_natCast x n
  simp only [zpair, V.pair.injEq] at h
  rw [zpair_neg, h.1, h.2]

/-- Dividing a canonical pair by a common divisor of its parts. -/
theorem zpair_ediv (p : ℤ) (g : ℕ) (hd : g ∣ p.natAbs) :
    zpair (p / g) = .pair (num (p.toNat / g)) (num ((-p).toNat / g)) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg p
  · rw [← Int.natCast_ediv]
    simp only [zpair, Int.toNat_natCast, Int.toNat_neg_natCast, Nat.zero_div, num_zero]
  · have hd' : (g : ℤ) ∣ (n : ℤ) := Int.natCast_dvd_natCast.mpr (by simpa using hd)
    rw [Int.neg_ediv_of_dvd hd', ← Int.natCast_ediv]
    simp only [zpair, Int.neg_neg, Int.toNat_natCast, Int.toNat_neg_natCast, Nat.zero_div, num_zero]

/-- `Y` reduces `{p, q}` (canonical `p`, `q ≥ 1`) to lowest terms: it computes the value standing
for the rational `p / q` (Mathlib's `Rat.normalize p q`). -/
theorem reduce_computes (p : ℤ) (q : ℕ) (hq : q ≠ 0) :
    Computes 'Y' [.pair (zpair p) (num q)] (qpair (Rat.normalize p q hq)) := by
  have hY := Y_computes p.toNat (-p).toNat q (Nat.pos_of_ne_zero hq)
  rw [Int.toNat_add_toNat_neg_eq_natAbs] at hY
  simp only [qpair, Rat.normalize_eq]
  rw [zpair_ediv p _ (Nat.gcd_dvd_left _ _)]
  exact hY

/-- `⊕` = `iajb⊙jaib⊙ARibjb*cY` adds rationals. -/
theorem qadd_computes (r s : ℚ) : Computes '⊕' [qpair r, qpair s] (qpair (r + s)) := by
  have hR := R_computes (r.num.toNat * s.den + (-r.num).toNat * 0 +
      (s.num.toNat * r.den + (-s.num).toNat * 0))
    (r.num.toNat * 0 + (-r.num).toNat * s.den + (s.num.toNat * 0 + (-s.num).toNat * r.den))
  rw [show ((r.num.toNat * s.den + (-r.num).toNat * 0 +
        (s.num.toNat * r.den + (-s.num).toNat * 0) : ℕ) : ℤ) -
      ((r.num.toNat * 0 + (-r.num).toNat * s.den + (s.num.toNat * 0 + (-s.num).toNat * r.den) : ℕ) : ℤ)
      = r.num * s.den + s.num * r.den by
    push_cast
    linear_combination (s.den : ℤ) * Int.toNat_sub_toNat_neg r.num +
      (r.den : ℤ) * Int.toNat_sub_toNat_neg s.num] at hR
  rw [Rat.add_def]
  exact ⟨_, rfl, .callOf (.one (.c (.callOf (.one (.callOf (.two
    (.callOf (.two (.a .i) (.b .j)) (smul_computes _ _ _))
    (.callOf (.two (.a .j) (.b .i)) (smul_computes _ _ _))) (A_computes _ _ _ _))) hR)
    (.callOf (.two (.b .i) (.b .j)) (times_computes _ _)))) (reduce_computes _ _ _)⟩

/-- `⊖` = `iajb⊙jaib⊙SRibjb*cY` subtracts rationals. -/
theorem qsub_computes (r s : ℚ) : Computes '⊖' [qpair r, qpair s] (qpair (r - s)) := by
  have hR := R_computes (r.num.toNat * s.den + (-r.num).toNat * 0 +
      (s.num.toNat * 0 + (-s.num).toNat * r.den))
    (r.num.toNat * 0 + (-r.num).toNat * s.den + (s.num.toNat * r.den + (-s.num).toNat * 0))
  rw [show ((r.num.toNat * s.den + (-r.num).toNat * 0 +
        (s.num.toNat * 0 + (-s.num).toNat * r.den) : ℕ) : ℤ) -
      ((r.num.toNat * 0 + (-r.num).toNat * s.den + (s.num.toNat * r.den + (-s.num).toNat * 0) : ℕ) : ℤ)
      = r.num * s.den - s.num * r.den by
    push_cast
    linear_combination (s.den : ℤ) * Int.toNat_sub_toNat_neg r.num -
      (r.den : ℤ) * Int.toNat_sub_toNat_neg s.num] at hR
  rw [Rat.sub_def]
  exact ⟨_, rfl, .callOf (.one (.c (.callOf (.one (.callOf (.two
    (.callOf (.two (.a .i) (.b .j)) (smul_computes _ _ _))
    (.callOf (.two (.a .j) (.b .i)) (smul_computes _ _ _))) (S_computes _ _ _ _))) hR)
    (.callOf (.two (.b .i) (.b .j)) (times_computes _ _)))) (reduce_computes _ _ _)⟩

/-- `⊗` = `iajaMibjb*cY` multiplies rationals. -/
theorem qmul_computes (r s : ℚ) : Computes '⊗' [qpair r, qpair s] (qpair (r * s)) := by
  have hM := M_computes r.num.toNat (-r.num).toNat s.num.toNat (-s.num).toNat
  rw [← zpair_mul] at hM
  rw [Rat.mul_def]
  exact ⟨_, rfl, .callOf (.one (.c (.callOf (.two (.a .i) (.a .j)) hM)
    (.callOf (.two (.b .i) (.b .j)) (times_computes _ _)))) (reduce_computes _ _ _)⟩

/-- `⊘` = `jabiajb⊙Niajb⊙dibjaajab+*cY` divides rationals (`r / s` for `s ≠ 0`): the numerator
is `r.num * s.den`, negated if `s < 0`, over `r.den * |s.num|`. -/
theorem qdiv_computes (r s : ℚ) (hs : s ≠ 0) : Computes '⊘' [qpair r, qpair s] (qpair (r / s)) := by
  have hsn : s.num ≠ 0 := fun h => hs (Rat.num_eq_zero.mp h)
  have hden : r.den * s.num.natAbs ≠ 0 := Nat.mul_ne_zero r.den_nz (Int.natAbs_ne_zero.mpr hsn)
  have hX := smul_computes r.num.toNat (-r.num).toNat s.den
  rw [Rat.div_def, Rat.mul_def', Rat.num_inv, Rat.den_inv]
  simp only [hsn, ↓reduceIte]
  rcases lt_or_gt_of_ne hsn with hneg | hpos
  · -- `s < 0`: the second part of `s.num` is a successor, and `d` takes the `N` branch
    obtain ⟨k, hk⟩ : ∃ k, (-s.num).toNat = k + 1 := ⟨(-s.num).toNat - 1, by omega⟩
    have hY := reduce_computes (-(r.num * s.den)) (r.den * s.num.natAbs) hden
    rw [Rat.normalize_eq_mkRat, zpair_neg_mul_natCast,
      ← Int.toNat_add_toNat_neg_eq_natAbs, hk] at hY
    rw [Int.sign_eq_neg_one_of_neg hneg,
      show r.num * (-1 * (s.den : ℤ)) = -(r.num * s.den) by ring,
      ← Int.toNat_add_toNat_neg_eq_natAbs, hk,
      show qpair s = .pair (.pair (num s.num.toNat) (.pair .atom (num k))) (num s.den) by
        simp [qpair, zpair, hk]]
    exact ⟨_, rfl, .callOf (.one (.c
      (.dT (.b (.a .j)) (.callOf (.one (.callOf (.two (.a .i) (.b .j)) hX)) (neg_computes _ _)))
      (.callOf (.two (.b .i) (.callOf (.two (.a (.a .j)) (.b (.a .j)))
        (plus_computes s.num.toNat (k + 1)))) (times_computes _ _)))) hY⟩
  · -- `s > 0`: the second part of `s.num` is `0`, and `d` takes the other branch
    have hk : (-s.num).toNat = 0 := by omega
    have hY := reduce_computes (r.num * s.den) (r.den * s.num.natAbs) hden
    rw [Rat.normalize_eq_mkRat, zpair_mul_natCast, ← Int.toNat_add_toNat_neg_eq_natAbs, hk] at hY
    rw [Int.sign_eq_one_of_pos hpos, show r.num * (1 * (s.den : ℤ)) = r.num * s.den by ring,
      ← Int.toNat_add_toNat_neg_eq_natAbs, hk,
      show qpair s = .pair (.pair (num s.num.toNat) .atom) (num s.den) by
        simp [qpair, zpair, hk]]
    exact ⟨_, rfl, .callOf (.one (.c
      (.dF (.b (.a .j)) (.callOf (.two (.a .i) (.b .j)) hX))
      (.callOf (.two (.b .i) (.callOf (.two (.a (.a .j)) (.b (.a .j)))
        (plus_computes s.num.toNat 0))) (times_computes _ _)))) hY⟩

/-! ## Binary naturals

A binary natural is the list of its bits, least significant first, without trailing zeros: the
bit `0` is the atom, the bit `1` is `{0, 0} = num 1`, and the list `[x₁, …, xₙ]` is
`{x₁, {x₂, … {xₙ, 0}}}`. So `0` is the atom, `1 = [1] = {{0,0}, 0}`, `2 = [0, 1]`, `5 = [1, 0, 1]`.
The programs `s` (successor), `p` (sum), `w` (doubling) and `m` (product) work on these lists,
and `β` / `ν` convert the unary numeral `num n` to the binary list and back. -/

/-- The bit `b`: `0` is the atom, `1` (any nonzero `b`) is `{0, 0} = num 1`. -/
def bit : ℕ → V
  | 0 => .atom
  | _ + 1 => num 1

/-- The canonical binary list of `n`: `bin 0 = 0`, `bin n = {bit (n % 2), bin (n / 2)}` for
`n ≠ 0`. -/
def bin (n : ℕ) : V :=
  if h : n = 0 then .atom else .pair (bit (n % 2)) (bin (n / 2))
decreasing_by omega

@[simp] theorem bin_zero : bin 0 = .atom := by
  rw [bin]; simp

theorem bin_of_ne_zero (n : ℕ) (h : n ≠ 0) : bin n = .pair (bit (n % 2)) (bin (n / 2)) := by
  rw [bin]; simp [h]

/-- The unfolding at an odd number: the first bit is `1`. -/
theorem bin_odd (n : ℕ) : bin (2 * n + 1) = .pair (num 1) (bin n) := by
  rw [bin_of_ne_zero (2 * n + 1) (by omega), show (2 * n + 1) % 2 = 1 by omega,
    show (2 * n + 1) / 2 = n by omega]
  rfl

/-- The unfolding at a positive even number: the first bit is `0`. -/
theorem bin_even (n : ℕ) : bin (2 * n + 2) = .pair .atom (bin (n + 1)) := by
  rw [bin_of_ne_zero (2 * n + 2) (by omega), show (2 * n + 2) % 2 = 0 by omega,
    show (2 * n + 2) / 2 = n + 1 by omega]
  rfl

theorem bin_two_mul (n : ℕ) (h : n ≠ 0) : bin (2 * n) = .pair .atom (bin n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, bin_even]

theorem bin_one : bin 1 = .pair (num 1) .atom := by
  simpa using bin_odd 0

/-- `s` = `iia0ibfc1ibcd10cd` is the binary successor: `[]` becomes `[1]`, a first bit `1`
becomes `0` with a carry into the rest (the recursive call), a first bit `0` becomes `1`. -/
theorem bs_computes (n : ℕ) : Computes 's' [bin n] (bin (n + 1)) := by
  refine ⟨_, rfl, ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [bin_zero, Nat.zero_add, bin_one]
    exact .dF .i (.c (.callOf .nil one_computes) .zero)
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 1 ∨ n = 2 * k + 2 := ⟨(n - 1) / 2, by omega⟩
  · rw [bin_odd k, show 2 * k + 1 + 1 = 2 * k + 2 by omega, bin_even k]
    exact .dT .i (.dT (.a .i) (.c .zero (.self (.one (.b .i)) (ih k (by omega)))))
  · rw [bin_even k, show 2 * k + 2 + 1 = 2 * (k + 1) + 1 by omega, bin_odd (k + 1)]
    exact .dT .i (.dF (.a .i) (.c (.callOf .nil one_computes) (.b .i)))

/-- `w` = `i0icid` doubles: it prepends the bit `0` to a nonempty list, and `0` stays `0`. -/
theorem bw_computes (n : ℕ) : Computes 'w' [bin n] (bin (2 * n)) := by
  refine ⟨_, rfl, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.mul_zero, bin_zero]; exact .dF .i .i
  · rw [bin_two_mul n (by omega), bin_of_ne_zero n (by omega)]
    exact .dT .i (.c .zero .i)

/-- `p` = `ijiaja0ibjbfsc1ibjbfcdja1ibjbfc0ibjbfcddidjd` is binary addition: if either list is
empty the sum is the other; otherwise the sum bit is prepended to the recursive sum of the tails,
`s` being applied to it when both first bits are `1`. -/
theorem bp_computes (m n : ℕ) : Computes 'p' [bin m, bin n] (bin (m + n)) := by
  refine ⟨_, rfl, ?_⟩
  induction m using Nat.strong_induction_on generalizing n with
  | _ m ih =>
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [bin_zero, Nat.zero_add]; exact .dF .i .j
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [bin_zero, Nat.add_zero, bin_of_ne_zero m (by omega)]; exact .dT .i (.dF .j .i)
  obtain ⟨a, rfl | rfl⟩ : ∃ a, m = 2 * a + 1 ∨ m = 2 * a + 2 := ⟨(m - 1) / 2, by omega⟩ <;>
  obtain ⟨b, rfl | rfl⟩ : ∃ b, n = 2 * b + 1 ∨ n = 2 * b + 2 := ⟨(n - 1) / 2, by omega⟩
  · -- first bits `1`, `1`: sum bit `0`, carry
    rw [bin_odd a, bin_odd b, show 2 * a + 1 + (2 * b + 1) = 2 * (a + b) + 2 by omega, bin_even]
    exact .dT .i (.dT .j (.dT (.a .i) (.dT (.a .j) (.c .zero (.callOf (.one (.self
      (.two (.b .i) (.b .j)) (ih a (by omega) b))) (bs_computes (a + b)))))))
  · -- first bits `1`, `0`: sum bit `1`
    rw [bin_odd a, bin_even b, show 2 * a + 1 + (2 * b + 2) = 2 * (a + (b + 1)) + 1 by omega,
      bin_odd]
    exact .dT .i (.dT .j (.dT (.a .i) (.dF (.a .j) (.c (.callOf .nil one_computes)
      (.self (.two (.b .i) (.b .j)) (ih a (by omega) (b + 1)))))))
  · -- first bits `0`, `1`: sum bit `1`
    rw [bin_even a, bin_odd b, show 2 * a + 2 + (2 * b + 1) = 2 * (a + 1 + b) + 1 by omega,
      bin_odd]
    exact .dT .i (.dT .j (.dF (.a .i) (.dT (.a .j) (.c (.callOf .nil one_computes)
      (.self (.two (.b .i) (.b .j)) (ih (a + 1) (by omega) b))))))
  · -- first bits `0`, `0`: sum bit `0`
    rw [bin_even a, bin_even b, show 2 * a + 2 + (2 * b + 2) = 2 * (a + b + 1) + 2 by omega,
      bin_even, show a + b + 1 + 1 = a + 1 + (b + 1) by omega]
    exact .dT .i (.dT .j (.dF (.a .i) (.dF (.a .j) (.c .zero
      (.self (.two (.b .i) (.b .j)) (ih (a + 1) (by omega) (b + 1)))))))

/-- `m` = `iiajibjfwpibjfwd0d` is binary multiplication: `0 * n = 0`, and otherwise with
`r = w (m (tail i) j)` the product is `p j r` if the first bit of `i` is `1` and `r` if it is `0`. -/
theorem bm_computes (m n : ℕ) : Computes 'm' [bin m, bin n] (bin (m * n)) := by
  refine ⟨_, rfl, ?_⟩
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [bin_zero, Nat.zero_mul, bin_zero]; exact .dF .i .zero
  obtain ⟨a, rfl | rfl⟩ : ∃ a, m = 2 * a + 1 ∨ m = 2 * a + 2 := ⟨(m - 1) / 2, by omega⟩
  · rw [bin_odd a, show (2 * a + 1) * n = n + 2 * (a * n) by ring]
    exact .dT .i (.dT (.a .i) (.callOf (.two .j (.callOf (.one (.self (.two (.b .i) .j)
      (ih a (by omega)))) (bw_computes (a * n)))) (bp_computes n (2 * (a * n)))))
  · rw [bin_even a, show (2 * a + 2) * n = 2 * ((a + 1) * n) by ring]
    exact .dT .i (.dF (.a .i) (.callOf (.one (.self (.two (.b .i) .j) (ih (a + 1) (by omega))))
      (bw_computes ((a + 1) * n))))

/-- `β` = `iibfs0d` converts unary to binary: `β (n + 1) = s (β n)`, `β 0 = 0`. -/
theorem beta_computes (n : ℕ) : Computes 'β' [num n] (bin n) := by
  refine ⟨_, rfl, ?_⟩
  induction n with
  | zero => rw [bin_zero]; exact .dF .i .zero
  | succ n ih => exact .dT .i (.callOf (.one (.self (.one (.b .i)) ih)) (bs_computes n))

/-- `ν` = `iibfibf+ia+0d` converts binary to unary: `ν [x, …] = (ν … + ν …) + x` (the bit
`{0, 0}` being the unary `1`), `ν 0 = 0`. -/
theorem nu_computes (n : ℕ) : Computes 'ν' [bin n] (num n) := by
  refine ⟨_, rfl, ?_⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [bin_zero]; exact .dF .i .zero
  obtain ⟨a, rfl | rfl⟩ : ∃ a, n = 2 * a + 1 ∨ n = 2 * a + 2 := ⟨(n - 1) / 2, by omega⟩
  · rw [bin_odd a, show 2 * a + 1 = a + a + 1 by omega]
    exact .dT .i (.callOf (.two (.callOf (.two (.self (.one (.b .i)) (ih a (by omega)))
      (.self (.one (.b .i)) (ih a (by omega)))) (plus_computes a a)) (.a .i))
      (plus_computes (a + a) 1))
  · rw [bin_even a, show 2 * a + 2 = a + 1 + (a + 1) + 0 by omega]
    exact .dT .i (.callOf (.two (.callOf (.two (.self (.one (.b .i)) (ih (a + 1) (by omega)))
      (.self (.one (.b .i)) (ih (a + 1) (by omega)))) (plus_computes (a + 1) (a + 1))) (.a .i))
      (plus_computes (a + 1 + (a + 1)) 0))

/-- Distinct naturals have distinct binary lists (by `ν` and determinism), so `β` and `ν` are
inverse bijections between the unary numerals and the canonical binary lists. -/
theorem bin_injective : Function.Injective bin := by
  intro m n h
  have h₁ := nu_computes m
  have h₂ := nu_computes n
  rw [← h] at h₂
  exact num_injective (Computes.det h₁ h₂)

/-! The binary operations correspond to the unary ones through `ν`: whatever `s`, `p`, `m`
return on binary lists, `ν` of it is what `↑`, `+`, `*` return on the unary numerals. -/

theorem nu_bs (n : ℕ) {v w : V} (hs : Computes 's' [bin n] v) (hν : Computes 'ν' [v] w) :
    Computes '↑' [num n] w := by
  rw [Computes.det hs (bs_computes n)] at hν
  rw [Computes.det hν (nu_computes (n + 1))]
  exact succ_computes n

theorem nu_bp (m n : ℕ) {v w : V} (hp : Computes 'p' [bin m, bin n] v)
    (hν : Computes 'ν' [v] w) : Computes '+' [num m, num n] w := by
  rw [Computes.det hp (bp_computes m n)] at hν
  rw [Computes.det hν (nu_computes (m + n))]
  exact plus_computes m n

theorem nu_bm (m n : ℕ) {v w : V} (hm : Computes 'm' [bin m, bin n] v)
    (hν : Computes 'ν' [v] w) : Computes '*' [num m, num n] w := by
  rw [Computes.det hm (bm_computes m n)] at hν
  rw [Computes.det hν (nu_computes (m * n))]
  exact times_computes m n

/-! ## A meta-circular evaluator

The program `ε` is an mLISP interpreter written in mLISP: `ε(t, args, D)` evaluates the *tree*
`t` (a value encoding an expression) on the argument list `args` with the definition list `D`.

**Trees.** Every node is `{op, {extra, args}}` (`node op extra args`): `op = 0` is the atom
expression `0`; `op = 1` is `c` (a pair), `args` being the list of the two encoded argument
trees; `op = 2` is an argument, `extra = num idx` (`0, 1, 2` for `i, j, k`); `op = 3, 4, 5` are
`a`, `b`, `d`, `args` the list of the encoded argument trees; `op = 6` is a call of definition
number `n`, `extra = num n`, `args` the list of encoded argument trees, and the recursive call
`f` encodes as a call of the definition's own number. (Equality being the ordinary program `e`
of the table, the tree of `e(x, y)` is a call node like any other.) Lists are nested pairs
ending in the atom (`listV`).
Definitions are numbered by their position in `table` (`ix`), the definition list `encD` is the
list of the trees of all programs of the table, and `encBody c` is the tree of the program of
`c`. `encE ix cur e` is the tree of the expression `e` inside the definition number `cur`.

**The programs.** `u` = `iibjbfjad` is the list index, `u(n, L) = L[n]`; `λ` =
`i00c0iaibf0cccc00cd` turns a list of trees `[t₁, …, tₘ]` into the tree of
`c(t₁, c(t₂, … c(tₘ, 0)))` (a chain of `c`-nodes ending in a zero node, `chainV`), whose value is
the list of the values of the `tᵢ`; and `ε` reads the `op` of its tree with `ia`, tests
`op - 1, …, op - 5` for zero with `iab`, `iabb`, …, and dispatches: an argument is looked up with
`u` in `args`; `a b c d` are applied (with the interpreter's own `a b c d`, so laziness of `d`
and undefinedness of `a 0` are inherited) to the recursive evaluations `ε(args[i], args, D)`
of the argument trees; and for a call, `u(extra, D)` is the tree of the callee, `ε(λ(args),
args, D)` the list of the argument values, and the result is `ε` of the callee tree on them.

**The theorems.** `u_computes`, `lambda_chain_computes`, `encD_lookup` describe the helpers;
`meta_zero`, `meta_arg`, …, `meta_call`, `meta_chain_cons` are the cases of `ε` (one per rule
of `Eval`); `Eval.meta` / `EvalList.meta` prove by induction on the
derivation that whenever `e` evaluates to `v` (in the body numbered `cur`, on `env`), `ε`
evaluates the tree of `e` on `listV env` and `encD` to the same `v`; `meta_sound` is the
statement for `Computes`: if the program `c` computes `v` on `args`, so does `ε` on the tree of
`c` (`meta_e`: in particular `ε` on the tree of `e` computes equality). With determinism,
`meta_det`: `ε` can only return the value the program returns. -/

/-- The list `[v₁, …, vₙ]` as nested pairs `{v₁, {v₂, … {vₙ, 0}}}`. -/
def listV : List V → V
  | [] => .atom
  | v :: vs => .pair v (listV vs)

@[simp] theorem listV_nil : listV [] = .atom := rfl
@[simp] theorem listV_cons (v : V) (vs : List V) : listV (v :: vs) = .pair v (listV vs) := rfl

/-- A tree node `{op, {extra, args}}`. -/
abbrev node (op : ℕ) (extra args : V) : V := .pair (num op) (.pair extra args)

mutual
  /-- The tree of an expression, inside the definition numbered `cur`, the defined symbols being
  numbered by `ix`. -/
  def encE (ix : Char → ℕ) (cur : ℕ) : E → V
    | .zero => node 0 .atom .atom
    | .c x y => node 1 .atom (.pair (encE ix cur x) (.pair (encE ix cur y) .atom))
    | .arg n => node 2 (num n) .atom
    | .a x => node 3 .atom (.pair (encE ix cur x) .atom)
    | .b x => node 4 .atom (.pair (encE ix cur x) .atom)
    | .d x y z =>
      node 5 .atom (.pair (encE ix cur x) (.pair (encE ix cur y) (.pair (encE ix cur z) .atom)))
    | .call name args => node 6 (num (ix name)) (encList ix cur args)
    | .self args => node 6 (num cur) (encList ix cur args)
  /-- The list of the trees of a list of expressions. -/
  def encList (ix : Char → ℕ) (cur : ℕ) : List E → V
    | [] => .atom
    | x :: xs => .pair (encE ix cur x) (encList ix cur xs)
end

/-- The symbols of the table in order: definition number `n` is `syms[n]`. -/
def syms : List Char := table.map Prod.fst

/-- The number of a defined symbol: its position in the table. -/
def ix (c : Char) : ℕ := syms.idxOf c

/-- The program of a symbol of the table (`0` for an undefined symbol). -/
def bodyOf (c : Char) : E := (defs c).getD .zero

/-- The tree of the program of the symbol `c`. -/
def encBody (c : Char) : V := encE ix (ix c) (bodyOf c)

/-- The definition list: the trees of all programs of the table, in order. -/
def encD : V := listV (syms.map encBody)

/-- The tree `λ` builds from a list of trees: `c(t₁, c(t₂, … c(tₘ, 0)))`. -/
def chainV : V → V
  | .atom => .pair .atom .atom
  | .pair t rest => node 1 .atom (.pair t (.pair (chainV rest) .atom))

/-- `b` iterated `k` times. -/
def E.bPow : ℕ → E → E
  | 0, x => x
  | k + 1, x => .b (E.bPow k x)

theorem EvalList.three {defs : Char → Option E} {body : E} {env : List V} {x y z : E} {u v w : V}
    (hx : Eval defs body env x u) (hy : Eval defs body env y v) (hz : Eval defs body env z w) :
    EvalList defs body env [x, y, z] [u, v, w] :=
  .cons hx (.cons hy (.cons hz .nil))

/-- Every symbol with a program is in the table. -/
theorem mem_syms_of_defs {c : Char} {e : E} (h : defs c = some e) : c ∈ syms := by
  unfold defs at h
  split at h <;> first | decide | exact absurd h (by simp)

/-- `u` = `iibjbfjad` is the list index: `u(n, L) = L[n]`. -/
theorem u_computes (n : ℕ) {L : List V} {v : V} (h : L[n]? = some v) :
    Computes 'u' [num n, listV L] v := by
  induction n generalizing L with
  | zero =>
    cases L with
    | nil => simp at h
    | cons w L => cases h; exact ⟨_, rfl, .dF .i (.a .j)⟩
  | succ n ih =>
    cases L with
    | nil => simp at h
    | cons w L =>
      exact ⟨_, rfl, .dT .i (.self (.two (.b .i) (.b .j)) ((ih h).eval rfl))⟩

/-- `λ` = `i00c0iaibf0cccc00cd` builds the chain of `c`-nodes of a list of trees. -/
theorem lambda_chain_computes (L : V) : Computes 'λ' [L] (chainV L) := by
  refine ⟨_, rfl, ?_⟩
  induction L with
  | atom => exact .dF .i (.c .zero .zero)
  | pair t rest _ ih =>
    exact .dT .i (.c (.c .zero .zero) (.c .zero (.c (.a .i) (.c (.self (.one (.b .i)) ih) .zero))))

/-- Looking up a definition in the definition list: `u(ix c, encD)` is the tree of `c`'s program. -/
theorem encD_lookup {c : Char} {e : E} (h : defs c = some e) :
    Computes 'u' [num (ix c), encD] (encE ix (ix c) e) := by
  have hlt : ix c < syms.length := List.idxOf_lt_length_of_mem (mem_syms_of_defs h)
  refine u_computes _ ?_
  rw [List.getElem?_map, List.getElem?_eq_some_iff.mpr ⟨hlt, rfl⟩, Option.map_some,
    show syms[ix c] = c from List.getElem_idxOf hlt]
  simp [encBody, bodyOf, h]

/-- Inside `ε`, with the tree `{op, p}` as `i`: `b^k (a i)` is `op - k`. -/
theorem Eval.opTest (k j : ℕ) {p : V} {body : E} {env : List V} :
    Eval defs body (.pair (num (k + j)) p :: env) (E.bPow k (.a .i)) (num j) := by
  induction k generalizing j with
  | zero => rw [Nat.zero_add]; exact .a .i
  | succ k ih => rw [show k + 1 + j = k + (j + 1) by omega]; exact .b (ih (j + 1))

/-! ### The cases of `ε`, one per rule of `Eval` -/

section MetaRules
variable {cur : ℕ} {L : V}

/-- `ε` on a zero node is `0`. -/
theorem meta_zero : Computes 'ε' [encE ix cur .zero, L, encD] .atom := ⟨_, rfl, .dF (.a .i) .zero⟩

/-- `ε` on an argument node looks the argument up with `u`. -/
theorem meta_arg {env : List V} {n : ℕ} {v : V} (h : env[n]? = some v) :
    Computes 'ε' [encE ix cur (.arg n), listV env, encD] v :=
  ⟨_, rfl, .dT (.a .i) (.dT (.opTest 1 1) (.dF (.opTest 2 0)
    (.callOf (.two (.a (.b .i)) .j) (u_computes _ h))))⟩

/-- `ε` on an `a`-node is `a` of `ε` on the argument tree. -/
theorem meta_a {x : E} {u w : V} (h : Computes 'ε' [encE ix cur x, L, encD] (.pair u w)) :
    Computes 'ε' [encE ix cur (.a x), L, encD] u :=
  ⟨_, rfl, .dT (.a .i) (.dT (.opTest 1 2) (.dT (.opTest 2 1) (.dF (.opTest 3 0)
    (.a (.self (.three (.a (.b (.b .i))) .j .k) (h.eval rfl))))))⟩

/-- `ε` on a `b`-node is `b` of `ε` on the argument tree. -/
theorem meta_b {x : E} {u w : V} (h : Computes 'ε' [encE ix cur x, L, encD] (.pair u w)) :
    Computes 'ε' [encE ix cur (.b x), L, encD] w :=
  ⟨_, rfl, .dT (.a .i) (.dT (.opTest 1 3) (.dT (.opTest 2 2) (.dT (.opTest 3 1)
    (.dF (.opTest 4 0) (.b (.self (.three (.a (.b (.b .i))) .j .k) (h.eval rfl)))))))⟩

/-- `ε` on a `c`-node is the pair of `ε` on the two argument trees. -/
theorem meta_c {x y : E} {u w : V} (hx : Computes 'ε' [encE ix cur x, L, encD] u)
    (hy : Computes 'ε' [encE ix cur y, L, encD] w) :
    Computes 'ε' [encE ix cur (.c x y), L, encD] (.pair u w) :=
  ⟨_, rfl, .dT (.a .i) (.dF (.opTest 1 0)
    (.c (.self (.three (.a (.b (.b .i))) .j .k) (hx.eval rfl))
      (.self (.three (.a (.b (.b (.b .i)))) .j .k) (hy.eval rfl))))⟩

/-- `ε` on a `d`-node whose condition is a pair is `ε` on the second argument tree. -/
theorem meta_dT {x y z : E} {u w v : V} (hx : Computes 'ε' [encE ix cur x, L, encD] (.pair u w))
    (hy : Computes 'ε' [encE ix cur y, L, encD] v) :
    Computes 'ε' [encE ix cur (.d x y z), L, encD] v :=
  ⟨_, rfl, .dT (.a .i) (.dT (.opTest 1 4) (.dT (.opTest 2 3) (.dT (.opTest 3 2)
    (.dT (.opTest 4 1) (.dF (.opTest 5 0)
      (.dT (.self (.three (.a (.b (.b .i))) .j .k) (hx.eval rfl))
        (.self (.three (.a (.b (.b (.b .i)))) .j .k) (hy.eval rfl))))))))⟩

/-- `ε` on a `d`-node whose condition is the atom is `ε` on the third argument tree. -/
theorem meta_dF {x y z : E} {v : V} (hx : Computes 'ε' [encE ix cur x, L, encD] .atom)
    (hz : Computes 'ε' [encE ix cur z, L, encD] v) :
    Computes 'ε' [encE ix cur (.d x y z), L, encD] v :=
  ⟨_, rfl, .dT (.a .i) (.dT (.opTest 1 4) (.dT (.opTest 2 3) (.dT (.opTest 3 2)
    (.dT (.opTest 4 1) (.dF (.opTest 5 0)
      (.dF (.self (.three (.a (.b (.b .i))) .j .k) (hx.eval rfl))
        (.self (.three (.a (.b (.b (.b (.b .i))))) .j .k) (hz.eval rfl))))))))⟩

/-- `ε` on a call node of definition `n`: look the callee's tree up with `u`, evaluate the
chain of the argument trees to the list of argument values, and run `ε` on the callee's tree
with them (the tree of `.call name args` and of `.self args` is such a node). -/
theorem meta_call {n : ℕ} {body : E} {args : List E} {vs : List V} {v : V}
    (hdef : Computes 'u' [num n, encD] (encE ix n body))
    (hargs : Computes 'ε' [chainV (encList ix cur args), L, encD] (listV vs))
    (hbody : Computes 'ε' [encE ix n body, listV vs, encD] v) :
    Computes 'ε' [node 6 (num n) (encList ix cur args), L, encD] v :=
  ⟨_, rfl, .dT (.a .i) (.dT (.opTest 1 5) (.dT (.opTest 2 4) (.dT (.opTest 3 3)
    (.dT (.opTest 4 2) (.dT (.opTest 5 1)
      (.self (.three (.callOf (.two (.a (.b .i)) .k) hdef)
          (.self (.three (.callOf (.one (.b (.b .i))) (lambda_chain_computes _)) .j .k)
            (hargs.eval rfl))
          .k)
        (hbody.eval rfl)))))))⟩

/-- `ε` on the chain of no trees is the empty list. -/
theorem meta_chain_nil : Computes 'ε' [chainV (encList ix cur []), L, encD] (listV []) :=
  ⟨_, rfl, .dF (.a .i) .zero⟩

/-- `ε` on the chain of the trees of `x :: xs` is the list of their values. -/
theorem meta_chain_cons {x : E} {xs : List E} {v : V} {vs : List V}
    (h : Computes 'ε' [encE ix cur x, L, encD] v)
    (hs : Computes 'ε' [chainV (encList ix cur xs), L, encD] (listV vs)) :
    Computes 'ε' [chainV (encList ix cur (x :: xs)), L, encD] (listV (v :: vs)) :=
  ⟨_, rfl, .dT (.a .i) (.dF (.opTest 1 0)
    (.c (.self (.three (.a (.b (.b .i))) .j .k) (h.eval rfl))
      (.self (.three (.a (.b (.b (.b .i)))) .j .k) (hs.eval rfl))))⟩

end MetaRules

mutual
  /-- Soundness of the interpreter: if `e` evaluates to `v` in the body numbered `cur` (so that
  `u(cur, encD)` is the tree of the body) on the arguments `env`, then `ε` evaluates the tree
  of `e` on `listV env` and `encD` to `v`. -/
  theorem Eval.meta : ∀ {body env e v}, Eval defs body env e v → ∀ {cur : ℕ},
      Computes 'u' [num cur, encD] (encE ix cur body) →
      Computes 'ε' [encE ix cur e, listV env, encD] v
    | _, _, _, _, .zero, _, _ => meta_zero
    | _, _, _, _, .arg h, _, _ => meta_arg h
    | _, _, _, _, .a h, _, hcur => meta_a (Eval.meta h hcur)
    | _, _, _, _, .b h, _, hcur => meta_b (Eval.meta h hcur)
    | _, _, _, _, .c hx hy, _, hcur => meta_c (Eval.meta hx hcur) (Eval.meta hy hcur)
    | _, _, _, _, .dT hx hy, _, hcur => meta_dT (Eval.meta hx hcur) (Eval.meta hy hcur)
    | _, _, _, _, .dF hx hz, _, hcur => meta_dF (Eval.meta hx hcur) (Eval.meta hz hcur)
    | _, _, _, _, .self hargs hbody, _, hcur =>
      meta_call hcur (EvalList.meta hargs hcur) (Eval.meta hbody hcur)
    | _, _, _, _, .call hdef hargs hbody, _, hcur =>
      meta_call (encD_lookup hdef) (EvalList.meta hargs hcur) (Eval.meta hbody (encD_lookup hdef))

  /-- The chain of `c`-nodes of the trees of `xs` evaluates to the list of the values of `xs`. -/
  theorem EvalList.meta : ∀ {body env xs vs}, EvalList defs body env xs vs → ∀ {cur : ℕ},
      Computes 'u' [num cur, encD] (encE ix cur body) →
      Computes 'ε' [chainV (encList ix cur xs), listV env, encD] (listV vs)
    | _, _, _, _, .nil, _, _ => meta_chain_nil
    | _, _, _, _, .cons h hs, _, hcur => meta_chain_cons (Eval.meta h hcur) (EvalList.meta hs hcur)
end

/-- `ε` is sound: whatever a program of the table computes, `ε` computes on its tree. -/
theorem meta_sound {c : Char} {args : List V} {v : V} (h : Computes c args v) :
    Computes 'ε' [encBody c, listV args, encD] v := by
  obtain ⟨e, he, h⟩ := h
  have := Eval.meta h (encD_lookup he)
  simpa [encBody, bodyOf, he] using this

/-- In particular `ε` on the tree of the program `e` computes equality. -/
theorem meta_e (x y : V) :
    Computes 'ε' [encE ix (ix 'e') eqBody, listV [x, y], encD] (if x = y then num 1 else .atom) := by
  simpa [encBody, bodyOf, defs_e] using meta_sound (eq_computes x y)

/-- By determinism, `ε` on the tree of `c` can only return what `c` returns. -/
theorem meta_det {c : Char} {args : List V} {v w : V} (h : Computes c args w)
    (hε : Computes 'ε' [encBody c, listV args, encD] v) : v = w :=
  Computes.det hε (meta_sound h)

/-- Executable checks of the interpreter on the trees of `+`, `*`, `Π`, of the program `ije`
(a call of `e` on `i` and `j`) and of `~` = `iEjEe`. -/
-- `ε` on the tree of `+`, checked inside the kernel.
example : run 300 'ε' [encBody '+', listV [num 2, num 3], encD] = some (num 5) := by decide

theorem meta_tests :
    run 1000 'ε' [encBody '+', listV [num 2, num 3], encD] = some (num 5) ∧
    run 1000 'ε' [encBody '*', listV [num 3, num 4], encD] = some (num 12) ∧
    run 5000 'ε' [encBody 'Π', listV [num 7], encD] = some (num 1) ∧
    run 5000 'ε' [encBody 'Π', listV [num 9], encD] = some (num 0) ∧
    run 1000 'ε' [encE ix 0 (.call 'e' [.i, .j]), listV [num 2, num 2], encD] = some (num 1) ∧
    run 1000 'ε' [encE ix 0 (.call 'e' [.i, .j]), listV [num 2, num 3], encD] = some (num 0) ∧
    run 2000 'ε' [encBody '~', listV [num 2, num 4], encD] = some (num 1) ∧
    run 2000 'ε' [encBody '~', listV [num 2, num 5], encD] = some (num 0) := by
  native_decide

/-! ## Executable tests

Everything above is proved for all inputs. The following checks additionally run the fuel
evaluator on small inputs and compare with Lean's own arithmetic on `ℕ`, `ℤ` and `ℚ`: an
independent cross-check of the evaluator, the encodings `num`/`zpair`/`qpair` and the table. The
naturals checks run inside the kernel (`decide`); the integer and rational checks use the compiled
evaluator (`native_decide`). -/

/-- The integers `-4 .. 4`. -/
def smallZ : List ℤ := (List.range 9).map fun (n : ℕ) => (n : ℤ) - 4

/-- The rationals `p / q` with `-3 ≤ p ≤ 3` and `1 ≤ q ≤ 3`. -/
def smallQ : List ℚ :=
  (List.range 7).flatMap fun (p : ℕ) =>
    (List.range 3).map fun (q : ℕ) => (((p : ℤ) - 3 : ℤ) : ℚ) / ((q : ℚ) + 1)

theorem nat_tests : ∀ m ∈ List.range 5, ∀ n ∈ List.range 5,
    run 300 '+' [num m, num n] = some (num (m + n)) ∧
    run 300 '*' [num m, num n] = some (num (m * n)) ∧
    run 300 '<' [num m, num n] = some (boolV (decide (m < n))) ∧
    run 300 '≤' [num m, num n] = some (boolV (decide (m ≤ n))) ∧
    run 300 '~' [num m, num n] = some (boolV (decide (m % 2 = n % 2))) ∧
    run 300 '%' [num m, num (n + 1)] = some (num (m % (n + 1))) ∧
    run 300 'Q' [num m, num (n + 1)] = some (num (m / (n + 1))) ∧
    run 300 'G' [num m, num n] = some (num (Nat.gcd m n)) ∧
    run 300 '|' [num (m + 1), num n] = some (boolV (decide ((m + 1) ∣ n))) := by
  decide

theorem int_tests : ∀ x ∈ smallZ, ∀ y ∈ smallZ,
    run 500 '⊞' [zpair x, zpair y] = some (zpair (x + y)) ∧
    run 500 '⊟' [zpair x, zpair y] = some (zpair (x - y)) ∧
    run 500 '⊠' [zpair x, zpair y] = some (zpair (x * y)) ∧
    run 500 'L' [zpair x, zpair y] = some (boolV (decide (x ≤ y))) ∧
    run 500 'V' [zpair x, zpair y] = some (boolV (decide (x ∣ y))) := by
  native_decide

theorem rat_tests : ∀ r ∈ smallQ, ∀ s ∈ smallQ,
    run 5000 '⊕' [qpair r, qpair s] = some (qpair (r + s)) ∧
    run 5000 '⊖' [qpair r, qpair s] = some (qpair (r - s)) ∧
    run 5000 '⊗' [qpair r, qpair s] = some (qpair (r * s)) ∧
    (s = 0 ∨ run 5000 '⊘' [qpair r, qpair s] = some (qpair (r / s))) ∧
    run 5000 '⊝' [qpair r] = some (qpair (-r)) ∧
    run 5000 '≼' [qpair r, qpair s] = some (boolV (decide (r ≤ s))) := by
  native_decide

theorem bin_tests : ∀ m ∈ List.range 7, ∀ n ∈ List.range 7,
    run 2000 's' [bin m] = some (bin (m + 1)) ∧
    run 2000 'w' [bin m] = some (bin (2 * m)) ∧
    run 2000 'p' [bin m, bin n] = some (bin (m + n)) ∧
    run 2000 'm' [bin m, bin n] = some (bin (m * n)) ∧
    run 2000 'β' [num m] = some (bin m) ∧
    run 2000 'ν' [bin m] = some (num m) := by
  native_decide

/-- `Y` reduces any pair `{canonical integer p, natural q ≥ 1}` to lowest terms. -/
theorem reduce_tests : ∀ p ∈ smallZ, ∀ q ∈ List.range 4,
    run 5000 'Y' [.pair (zpair p) (num (q + 1))] = some (qpair ((p : ℚ) / (q + 1 : ℕ))) := by
  native_decide

end MLISP
