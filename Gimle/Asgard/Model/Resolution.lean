import Gimle.Asgard.Model.Declaration

/-! Proof-carrying resolution of original, unordered named equations. The source
relation quantifies real environments and never executes a target circuit. -/
namespace Gimle.Asgard.Model
open Polynomial

/-- Agreement is required only at defined names, not on unrelated variables. -/
def Agrees {α : Type} (a b : String → Option α) : Prop :=
  ∀ name value, a name = some value → b name = some value

theorem eval_agrees (e : NamedExpr) {a b : String → Option ℝ} (h : Agrees a b)
    {value : ℝ} (he : e.eval a = some value) : e.eval b = some value := by
  induction e generalizing value with
  | var name => exact h name value he
  | constant q => exact he
  | neg e ih =>
      cases hv : e.eval a with
      | none => simp [NamedExpr.eval, hv] at he
      | some v =>
          simpa [NamedExpr.eval, ih hv] using
            (show some (-v) = some value by simpa [NamedExpr.eval, hv] using he)
  | add l r hl hr =>
      cases hv : l.eval a with
      | none => simp [NamedExpr.eval, hv] at he
      | some v =>
        cases hw : r.eval a with
        | none => simp [NamedExpr.eval, hv, hw] at he
        | some w =>
          simpa [NamedExpr.eval, hl hv, hr hw] using
            (show some (v + w) = some value by simpa [NamedExpr.eval, hv, hw] using he)
  | mul l r hl hr =>
      cases hv : l.eval a with
      | none => simp [NamedExpr.eval, hv] at he
      | some v =>
        cases hw : r.eval a with
        | none => simp [NamedExpr.eval, hv, hw] at he
        | some w =>
          simpa [NamedExpr.eval, hl hv, hr hw] using
            (show some (v * w) = some value by simpa [NamedExpr.eval, hv, hw] using he)

noncomputable def Evaluated {n : Nat} (env : String → Option (Expr n)) (x : Point n) : String → Option ℝ :=
  fun name => (env name).map (Expr.eval x)

theorem resolve_in {n : Nat} (e : NamedExpr) (env : String → Option (Expr n))
    (x : Point n) (source : String → Option ℝ) (h : Agrees (Evaluated env x) source)
    (value : Expr n) (found : e.resolve env = some value) :
    e.eval source = some (value.eval x) := by
  apply eval_agrees e h
  have correct := e.resolve_correct env x
  rw [found] at correct
  exact correct.symm

/-- Every original equation is retained, even if it is not an observable. -/
def Equations (assignments : List Assignment) (env : String → Option ℝ) : Prop :=
  ∀ a ∈ assignments, env a.output.name ≠ none ∧ a.rhs.eval env = env a.output.name

/-- Each step records the original assignment and the checked substitution.
Freshness ensures later steps cannot overwrite earlier inputs or assignments. -/
inductive Trace {n : Nat} (assignments : List Assignment)
    (seed : String → Option (Expr n)) : (String → Option (Expr n)) → Type where
  | start : Trace assignments seed seed
  | step {env} (previous : Trace assignments seed env) (a : Assignment)
      (member : a ∈ assignments) (value : Expr n)
      (fresh : env a.output.name = none) (resolved : a.rhs.resolve env = some value) :
      Trace assignments seed (Polynomial.bind env a.output.name value)

theorem Trace.extends {n : Nat} {as : List Assignment} {seed env : String → Option (Expr n)}
    (trace : Trace as seed env) : Agrees seed env := by
  induction trace with
  | start => intro name value h; exact h
  | step previous a member value fresh resolved ih =>
      intro name e h
      have old := ih name e h
      have ne : name ≠ a.output.name := by
        intro same
        subst name
        rw [fresh] at old
        contradiction
      simpa [Polynomial.bind, ne] using old

theorem Trace.forced {n : Nat} {as : List Assignment} {seed env : String → Option (Expr n)}
    (trace : Trace as seed env) (x : Point n) (source : String → Option ℝ)
    (initial : Agrees (Evaluated seed x) source) (equations : Equations as source) :
    Agrees (Evaluated env x) source := by
  induction trace with
  | start => exact initial
  | step previous a member value fresh resolved ih =>
      have hv := resolve_in a.rhs _ x source ih value resolved
      rw [(equations a member).2] at hv
      intro name v h
      by_cases same : name = a.output.name
      · subst name
        simp [Evaluated, Polynomial.bind] at h
        simpa [h] using hv
      · exact ih name v (by simpa [Evaluated, Polynomial.bind, same] using h)

structure Ready {n : Nat} (as : List Assignment) (env : String → Option (Expr n)) where
  assignment : Assignment
  member : assignment ∈ as
  value : Expr n
  fresh : env assignment.output.name = none
  resolved : assignment.rhs.resolve env = some value

/-- Stable tie-breaking: choose the first unresolved ready assignment in source order. -/
def nextReady {n : Nat} (as : List Assignment) (env : String → Option (Expr n)) :
    Option (Ready as env) :=
  as.attach.findSome? fun a =>
    if fresh : env a.val.output.name = none then
      match resolved : a.val.rhs.resolve env with
      | none => none
      | some value => some ⟨a.val, a.property, value, fresh, resolved⟩
    else none

structure Resolution {n : Nat} (as : List Assignment) (seed : String → Option (Expr n)) where
  env : String → Option (Expr n)
  trace : Trace as seed env

def schedule {n : Nat} {as : List Assignment} {seed : String → Option (Expr n)} :
    Nat → Resolution as seed → Resolution as seed
  | 0, result => result
  | fuel + 1, result =>
      match nextReady as result.env with
      | none => result
      | some ready => schedule fuel ⟨Polynomial.bind result.env ready.assignment.output.name ready.value,
          .step result.trace ready.assignment ready.member ready.value ready.fresh ready.resolved⟩

/-- A finite final check retains the equations needed for the reverse theorem. -/
def Complete {n : Nat} (as : List Assignment) (env : String → Option (Expr n)) : Prop :=
  ∀ a ∈ as, env a.output.name ≠ none ∧ a.rhs.resolve env = env a.output.name

instance {n : Nat} (as : List Assignment) (env : String → Option (Expr n)) :
    Decidable (Complete as env) := by unfold Complete; infer_instance

theorem complete_equations {n : Nat} (as : List Assignment)
    (env : String → Option (Expr n)) (complete : Complete as env) (x : Point n) :
    Equations as (Evaluated env x) := by
  intro a member
  constructor
  · cases found : env a.output.name with
    | none => exact False.elim ((complete a member).1 found)
    | some value => simp [Evaluated, found]
  · have correct := a.rhs.resolve_correct env x
    rw [(complete a member).2] at correct
    exact correct.symm

#print axioms Trace.forced
#print axioms complete_equations
end Gimle.Asgard.Model
