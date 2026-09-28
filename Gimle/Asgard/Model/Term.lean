import Gimle.Asgard.Model.Declaration

/-! Source terms of common declarations: named polynomial expressions, applied
scalar lambdas, derivative atoms and integrals from the declared start.

A lambda occurs only at its application site, `(λ x => body)(argument)`, as in
`Normalization.Source`; first-class and higher-order functions are outside the
fragment. Binding is lexical: the body sees the argument under the binder and
every other name from the enclosing scope. The argument is passed by name
(`rebind`), so beta reduction preserves meaning exactly, including an unused
argument that mentions an undefined name.

A derivative atom has no value of its own. A chain `D_a(D_b(… D_c(state)))`
is read as a whole: the caller supplies `rates`, which receives the axes from
the outermost inwards and the state name, and `Model.Differential` fixes it to
the declared derivative ports. A lambda binder shadows a state of the same name
for derivatives too, so `(λ x => D_t(x))(y)` has no value. A derivative of
anything other than a chain ending in a free name, and every integral, is a
non-local atom: its value at one time depends on the whole trajectory, so the
caller supplies it through `atoms`. `Model.Integral` gives the trajectory
reading (`Term.along`), where an integral is the antiderivative from the
declared start and a derivative of a non-chain is the actual derivative; under a
lambda binder, an atom mentioning the binder has no value. -/
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
  | integral (axis : String) (operand : Term)
  deriving Repr, DecidableEq

/-- Lexical rebinding of one name to a possibly undefined value. -/
def rebind {α : Type} (env : String → Option α) (name : String) (value : Option α) :
    String → Option α :=
  fun key => if key = name then value else env key

/-- A derivative chain `D_a(D_b(… state))` as its axes, outermost first, and
the differentiated name; a bare name is the empty chain. -/
def Term.chain : Term → Option (List String × String)
  | .var name => some ([], name)
  | .derivative axis operand => operand.chain.map fun (axes, name) => (axis :: axes, name)
  | _ => none

/-- Whether `name` occurs free, outside any binder of the same name. -/
def Term.mentions (name : String) : Term → Bool
  | .var n => n == name
  | .constant _ => false
  | .add a b | .mul a b => a.mentions name || b.mentions name
  | .neg a => a.mentions name
  | .apply x body arg => arg.mentions name || (x != name && body.mentions name)
  | .derivative _ operand | .integral _ operand => operand.mentions name

/-- Independent source semantics. `rates axes state` interprets the chain
`D_axes(state)`, axes outermost first; `rates [a] x` is `D_a(x)`. `atoms`
interprets the non-local atoms: every integral, and every derivative whose
operand is not a chain. Under a binder `x`, an atom that mentions `x` has no
value, as a chain based on `x` has none. -/
noncomputable def Term.eval (env : String → Option ℝ)
    (rates : List String → String → Option ℝ) (atoms : Term → Option ℝ) : Term → Option ℝ
  | .var name => env name
  | .constant q => some q
  | .add a b => do return (← a.eval env rates atoms) + (← b.eval env rates atoms)
  | .mul a b => do return (← a.eval env rates atoms) * (← b.eval env rates atoms)
  | .neg a => do return -(← a.eval env rates atoms)
  | .apply x body arg =>
      body.eval (rebind env x (arg.eval env rates atoms))
        (fun a s => if s = x then none else rates a s)
        (fun u => if u.mentions x then none else atoms u)
  | .derivative axis operand =>
      match operand.chain with
      | some (axes, state) => rates (axis :: axes) state
      | none => atoms (.derivative axis operand)
  | .integral axis operand => atoms (.integral axis operand)

/-- Number of derivative nodes, counting nested ones separately. -/
def Term.derivatives : Term → Nat
  | .var _ | .constant _ => 0
  | .add a b | .mul a b => a.derivatives + b.derivatives
  | .neg a => a.derivatives
  | .apply _ body arg => body.derivatives + arg.derivatives
  | .derivative _ operand => operand.derivatives + 1
  | .integral _ operand => operand.derivatives

/-- Number of integral nodes, counting nested ones separately. -/
def Term.integrals : Term → Nat
  | .var _ | .constant _ => 0
  | .add a b | .mul a b => a.integrals + b.integrals
  | .neg a => a.integrals
  | .apply _ body arg => body.integrals + arg.integrals
  | .derivative _ operand => operand.integrals
  | .integral _ operand => operand.integrals + 1

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
no free name can be captured. A derivative or an integral anywhere returns `none`. -/
def Term.beta : Term → Option NamedExpr
  | .var name => some (.var name)
  | .constant q => some (.constant q)
  | .add a b => do return .add (← a.beta) (← b.beta)
  | .mul a b => do return .mul (← a.beta) (← b.beta)
  | .neg a => do return .neg (← a.beta)
  | .apply x body arg => do return (← body.beta).subst x (← arg.beta)
  | .derivative _ _ | .integral _ _ => none

/-- Beta normalization preserves meaning exactly, for every environment:
defined and undefined values alike, and whatever derivative or atom
interpretation. -/
theorem Term.beta_correct (t : Term) (e : NamedExpr) (h : t.beta = some e)
    (env : String → Option ℝ) (rates : List String → String → Option ℝ)
    (atoms : Term → Option ℝ) :
    e.eval env = t.eval env rates atoms := by
  induction t generalizing e env rates atoms with
  | var name => cases h; rfl
  | constant q => cases h; rfl
  | add a b ha hb =>
      cases hA : a.beta <;> cases hB : b.beta <;> simp [beta, hA, hB] at h
      subst h
      simp [NamedExpr.eval, Term.eval, ha _ hA env rates atoms, hb _ hB env rates atoms]
  | mul a b ha hb =>
      cases hA : a.beta <;> cases hB : b.beta <;> simp [beta, hA, hB] at h
      subst h
      simp [NamedExpr.eval, Term.eval, ha _ hA env rates atoms, hb _ hB env rates atoms]
  | neg a ha =>
      cases hA : a.beta <;> simp [beta, hA] at h
      subst h
      simp [NamedExpr.eval, Term.eval, ha _ hA env rates atoms]
  | apply x body arg hbody harg =>
      cases hB : body.beta <;> cases hA : arg.beta <;> simp [beta, hB, hA] at h
      subst h
      rw [NamedExpr.subst_eval, Term.eval, hbody _ hB, harg _ hA env rates atoms]
  | derivative axis operand _ => simp [beta] at h
  | integral axis operand _ => simp [beta] at h

/-- An exact signed literal product, such as `-2 * rat(1,4)`. Sums of literals
are deliberately not scales, matching the pinned Python fragment. -/
def Term.literal : Term → Option ℚ
  | .constant q => some q
  | .neg a => a.literal.map (- ·)
  | .mul a b => do return (← a.literal) * (← b.literal)
  | _ => none

theorem Term.literal_correct (t : Term) (q : ℚ) (h : t.literal = some q)
    (env : String → Option ℝ) (rates : List String → String → Option ℝ)
    (atoms : Term → Option ℝ) :
    t.eval env rates atoms = some (q : ℝ) := by
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
only, never of their argument. The operand of a derivative or an integral is
checked the same way. -/
def Term.checkScope (names : List String) : Term → Except String Unit
  | .var name => if names.contains name then .ok () else .error name
  | .constant _ => .ok ()
  | .add a b | .mul a b => do a.checkScope names; b.checkScope names
  | .neg a => a.checkScope names
  | .apply x body arg => do arg.checkScope names; body.checkScope (x :: names)
  | .derivative _ operand | .integral _ operand => operand.checkScope names

#print axioms NamedExpr.subst_eval
#print axioms Term.beta_correct
#print axioms Term.literal_correct
end Gimle.Asgard.Model
