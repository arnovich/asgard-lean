import Gimle.Asgard.Model.Declaration

/-! Source terms of common declarations: named polynomial expressions, applied
scalar lambdas and derivative atoms.

A lambda occurs only at its application site, `(λ x => body)(argument)`, as in
`Normalization.Source`; first-class and higher-order functions are outside the
fragment. Binding is lexical: the body sees the argument under the binder and
every other name from the enclosing scope. The argument is passed by name
(`rebind`), so beta reduction preserves meaning exactly, including an unused
argument that mentions an undefined name.

A derivative atom `D_axis(state)` has no value of its own: the caller supplies
`rates`, and `Model.Differential` fixes it to the declared derivative of the
state. Every other derivative form evaluates to `none` here; it is outside the
fragment, and the isolation pass rejects it with a diagnostic rather than
giving it a meaning. -/
namespace Gimle.Asgard.Model
open Polynomial

inductive Term where
  | var (name : String)
  | constant (value : ℚ)
  | add (left right : Term)
  | mul (left right : Term)
  | neg (argument : Term)
  | apply (binder : String) (body argument : Term)
  | derivative (axis : String) (operand : Term)
  deriving Repr, DecidableEq

/-- Lexical rebinding of one name to a possibly undefined value. -/
def rebind {α : Type} (env : String → Option α) (name : String) (value : Option α) :
    String → Option α :=
  fun key => if key = name then value else env key

/-- Independent source semantics. `rates axis state` interprets `D_axis(state)`. -/
noncomputable def Term.eval (env : String → Option ℝ)
    (rates : String → String → Option ℝ) : Term → Option ℝ
  | .var name => env name
  | .constant q => some q
  | .add a b => do return (← a.eval env rates) + (← b.eval env rates)
  | .mul a b => do return (← a.eval env rates) * (← b.eval env rates)
  | .neg a => do return -(← a.eval env rates)
  | .apply x body arg => body.eval (rebind env x (arg.eval env rates)) rates
  | .derivative axis operand =>
      match operand with
      | .var state => rates axis state
      | _ => none

/-- Number of derivative nodes, counting nested ones separately. -/
def Term.derivatives : Term → Nat
  | .var _ | .constant _ => 0
  | .add a b | .mul a b => a.derivatives + b.derivatives
  | .neg a => a.derivatives
  | .apply _ body arg => body.derivatives + arg.derivatives
  | .derivative _ operand => operand.derivatives + 1

/-- Capture-free substitution: a `NamedExpr` has no binders. -/
def _root_.Gimle.Asgard.Polynomial.NamedExpr.subst (e : NamedExpr) (name : String)
    (value : NamedExpr) : NamedExpr :=
  match e with
  | .var n => if n = name then value else .var n
  | .constant q => .constant q
  | .add a b => .add (a.subst name value) (b.subst name value)
  | .mul a b => .mul (a.subst name value) (b.subst name value)
  | .neg a => .neg (a.subst name value)

theorem _root_.Gimle.Asgard.Polynomial.NamedExpr.subst_eval (e : NamedExpr) (name : String)
    (value : NamedExpr) (env : String → Option ℝ) :
    (e.subst name value).eval env = e.eval (rebind env name (value.eval env)) := by
  induction e with
  | var n => by_cases h : n = name <;> simp [NamedExpr.subst, NamedExpr.eval, rebind, h]
  | constant q => rfl
  | add a b ha hb => simp only [NamedExpr.subst, NamedExpr.eval, ha, hb]
  | mul a b ha hb => simp only [NamedExpr.subst, NamedExpr.eval, ha, hb]
  | neg a ha => simp only [NamedExpr.subst, NamedExpr.eval, ha]

/-- Scoped beta normalization of a derivative-free term. Inner binders are
normalized first, so substitution only ever acts on binder-free expressions and
no free name can be captured. A derivative anywhere returns `none`. -/
def Term.beta : Term → Option NamedExpr
  | .var name => some (.var name)
  | .constant q => some (.constant q)
  | .add a b => do return .add (← a.beta) (← b.beta)
  | .mul a b => do return .mul (← a.beta) (← b.beta)
  | .neg a => do return .neg (← a.beta)
  | .apply x body arg => do return (← body.beta).subst x (← arg.beta)
  | .derivative _ _ => none

/-- Beta normalization preserves meaning exactly, for every environment:
defined and undefined values alike, and whatever derivative interpretation. -/
theorem Term.beta_correct (t : Term) (e : NamedExpr) (h : t.beta = some e)
    (env : String → Option ℝ) (rates : String → String → Option ℝ) :
    e.eval env = t.eval env rates := by
  induction t generalizing e env with
  | var name => cases h; rfl
  | constant q => cases h; rfl
  | add a b ha hb =>
      cases hA : a.beta <;> cases hB : b.beta <;> simp [beta, hA, hB] at h
      subst h
      simp [NamedExpr.eval, Term.eval, ha _ hA, hb _ hB]
  | mul a b ha hb =>
      cases hA : a.beta <;> cases hB : b.beta <;> simp [beta, hA, hB] at h
      subst h
      simp [NamedExpr.eval, Term.eval, ha _ hA, hb _ hB]
  | neg a ha =>
      cases hA : a.beta <;> simp [beta, hA] at h
      subst h
      simp [NamedExpr.eval, Term.eval, ha _ hA]
  | apply x body arg hbody harg =>
      cases hB : body.beta <;> cases hA : arg.beta <;> simp [beta, hB, hA] at h
      subst h
      rw [NamedExpr.subst_eval, Term.eval, hbody _ hB, harg _ hA]
  | derivative axis operand _ => simp [beta] at h

theorem Term.beta_isSome (t : Term) (h : t.derivatives = 0) : (t.beta).isSome := by
  induction t with
  | var _ | constant _ => rfl
  | add a b ha hb | mul a b ha hb =>
      simp only [derivatives, Nat.add_eq_zero_iff] at h
      obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp (ha h.1)
      obtain ⟨eb, heb⟩ := Option.isSome_iff_exists.mp (hb h.2)
      simp [beta, hea, heb]
  | neg a ha =>
      obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp (ha h)
      simp [beta, hea]
  | apply x body arg hb ha =>
      simp only [derivatives, Nat.add_eq_zero_iff] at h
      obtain ⟨eb, heb⟩ := Option.isSome_iff_exists.mp (hb h.1)
      obtain ⟨ea, hea⟩ := Option.isSome_iff_exists.mp (ha h.2)
      simp [beta, heb, hea]
  | derivative => simp [derivatives] at h

/-- An exact signed literal product, such as `-2 * rat(1,4)`. Sums of literals
are deliberately not scales, matching the pinned Python fragment. -/
def Term.literal : Term → Option ℚ
  | .constant q => some q
  | .neg a => a.literal.map (- ·)
  | .mul a b => do return (← a.literal) * (← b.literal)
  | _ => none

theorem Term.literal_correct (t : Term) (q : ℚ) (h : t.literal = some q)
    (env : String → Option ℝ) (rates : String → String → Option ℝ) :
    t.eval env rates = some (q : ℝ) := by
  induction t generalizing q with
  | constant c => cases h; rfl
  | neg a ha =>
      cases hA : a.literal <;> simp [literal, hA] at h
      subst h
      simp [Term.eval, ha _ hA]
  | mul a b ha hb =>
      cases hA : a.literal <;> cases hB : b.literal <;> simp [literal, hA, hB] at h
      subst h
      simp [Term.eval, ha _ hA, hb _ hB]
  | _ => simp [literal] at h

/-- Every free name must be declared. Binders extend the scope of their body
only, never of their argument. A derivative's operand is checked the same way. -/
def Term.checkScope (names : List String) : Term → Except String Unit
  | .var name => if names.contains name then .ok () else .error name
  | .constant _ => .ok ()
  | .add a b | .mul a b => do a.checkScope names; b.checkScope names
  | .neg a => a.checkScope names
  | .apply x body arg => do arg.checkScope names; body.checkScope (x :: names)
  | .derivative _ operand => operand.checkScope names

#print axioms NamedExpr.subst_eval
#print axioms Term.beta_correct
#print axioms Term.literal_correct
end Gimle.Asgard.Model
