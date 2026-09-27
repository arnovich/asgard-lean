import Gimle.Asgard.Model.Term

/-! Bounded first-order differential isolation.

One source equation `lhs = rhs` in which exactly one side contains exactly one
derivative atom, of the form `q*D_t(x) + r = rhs`. The scale `q` is an exact
nonzero signed literal product and `r` and `rhs` are derivative-free
polynomial terms, with applied lambdas allowed. It is isolated to
`D_t(x) = (rhs - r)/q` with every residual term retained: nothing is
cancelled, integrated or dropped.

The atom is replaced by the declared derivative port of `x`; the equation is
then an ordinary assignment to that port. The axis, start and initial values
are not touched by this pass. They stay in the unchanged `Evolution`, and the
initialized feedback of `Model.Continuous` closes the result. There is no
integral in this fragment, so no inverse rewrite exists that could erase a
boundary term.

Rejected, each with its own diagnostic, never as a claim of unsatisfiability:
zero scale, competing atoms on both sides, repeated atoms on one side,
non-literal or nonlinear factors, a scale around a sum, higher-order, mixed-axis
and non-state derivatives, derivatives inside lambda applications, and
derivatives outside differential equations. -/
namespace Gimle.Asgard.Model
open Polynomial

/-- `axis` is the evolution axis display name; `locate` maps a state display
name to the display name of its declared derivative port. -/
structure Context where
  axis : String
  locate : String → Option String

/-- `D_axis(x)` denotes the value of `x`'s derivative port, and nothing on
another axis. `SourceBody.Solves` ties that port to the actual derivative. -/
def Context.rates {α : Type} (c : Context) (env : String → Option α) :
    String → String → Option α :=
  fun axis state => if axis = c.axis then (c.locate state).bind env else none

/-- A context with no derivatives: every atom is rejected by isolation. -/
def Context.empty : Context := ⟨"", fun _ => none⟩

/-- Classify every derivative node, before counting. -/
def Term.checkDerivatives (c : Context) : Term → Except ErrorCode Unit
  | .var _ | .constant _ => .ok ()
  | .add a b | .mul a b => do a.checkDerivatives c; b.checkDerivatives c
  | .neg a => a.checkDerivatives c
  | .apply _ body arg =>
      if body.derivatives + arg.derivatives = 0 then .ok () else .error .unsupportedDerivative
  | .derivative axis operand =>
      match operand with
      | .var state =>
          if axis ≠ c.axis then .error .mixedDerivative
          else if (c.locate state).isNone then .error .unsupportedDerivative
          else .ok ()
      | .derivative inner _ =>
          if axis ≠ inner ∨ axis ≠ c.axis then .error .mixedDerivative
          else .error .higherOrderDerivative
      | _ => .error .unsupportedDerivative

/-- One side, read as `scale * D_axis(state) + remainder`; `none` means no
remainder term was written. -/
structure Affine where
  axis : String
  state : String
  scale : ℚ
  remainder : Option NamedExpr

noncomputable def Affine.value (p : Affine) (env : String → Option ℝ) (rate : ℝ) :
    Option ℝ :=
  match p.remainder with
  | none => some (p.scale * rate)
  | some r => (r.eval env).map (fun y => p.scale * rate + y)

private def plusLeft (l : NamedExpr) : Option NamedExpr → NamedExpr
  | none => l
  | some r => .add l r

private def plusRight (r : NamedExpr) : Option NamedExpr → NamedExpr
  | none => r
  | some l => .add l r

/-- Recognize a side containing exactly one derivative atom. Additive
derivative-free terms become the remainder, in source order; a scale is an
exact literal factor of a bare scaled atom. -/
def Term.affine : Term → Except ErrorCode Affine
  | .derivative axis operand =>
      match operand with
      | .var state => .ok ⟨axis, state, 1, none⟩
      | .derivative _ _ => .error .higherOrderDerivative
      | _ => .error .unsupportedDerivative
  | .neg a => do
      let p ← a.affine
      return ⟨p.axis, p.state, -p.scale, p.remainder.map .neg⟩
  | .add a b =>
      if a.derivatives = 0 then
        match a.beta with
        | none => .error .unsupportedDerivative
        | some l => do
            let p ← b.affine
            return ⟨p.axis, p.state, p.scale, some (plusLeft l p.remainder)⟩
      else if b.derivatives = 0 then
        match b.beta with
        | none => .error .unsupportedDerivative
        | some r => do
            let p ← a.affine
            return ⟨p.axis, p.state, p.scale, some (plusRight r p.remainder)⟩
      else .error .repeatedDerivative
  | .mul a b =>
      match a.literal, b.literal with
      | some c, _ => do
          let p ← b.affine
          if p.remainder.isSome then .error .unsupportedDerivative
          else return ⟨p.axis, p.state, c * p.scale, none⟩
      | none, some c => do
          let p ← a.affine
          if p.remainder.isSome then .error .unsupportedDerivative
          else return ⟨p.axis, p.state, p.scale * c, none⟩
      | none, none => .error .nonlinearDerivative
  | .apply _ _ _ => .error .unsupportedDerivative
  | .var _ | .constant _ => .error .missingDerivative

theorem Term.affine_correct (t : Term) (p : Affine) (h : t.affine = .ok p)
    (env : String → Option ℝ) (rates : String → String → Option ℝ) (rate : ℝ)
    (hrate : rates p.axis p.state = some rate) : t.eval env rates = p.value env rate := by
  induction t generalizing p with
  | var _ | constant _ => simp [affine] at h
  | apply => simp [affine] at h
  | derivative axis operand _ =>
      cases operand <;> simp [affine] at h
      subst h
      simp [Term.eval, Affine.value, hrate]
  | neg a ha =>
      cases hA : a.affine with
      | error e => simp [affine, hA] at h
      | ok q =>
          simp [affine, hA] at h
          subst h
          have := ha q hA hrate
          simp only [Term.eval, this, Affine.value]
          cases hr : q.remainder with
          | none => simp
          | some r =>
              cases hv : r.eval env <;> simp [NamedExpr.eval, hv]
              ring
  | add a b ha hb =>
      by_cases za : a.derivatives = 0
      · cases hl : a.beta with
        | none => simp [affine, za, hl] at h
        | some l =>
          cases hB : b.affine with
          | error e => simp [affine, za, hl, hB] at h
          | ok q =>
            simp [affine, za, hl, hB] at h
            subst h
            simp only [Term.eval, ← a.beta_correct l hl env rates, hb q hB hrate]
            cases hr : q.remainder with
            | none =>
                cases hv : l.eval env <;> simp [Affine.value, hr, plusLeft, hv]
                ring
            | some r =>
                cases hv : l.eval env <;> cases hw : r.eval env <;>
                  simp [Affine.value, hr, plusLeft, NamedExpr.eval, hv, hw]
                ring
      · by_cases zb : b.derivatives = 0
        · cases hr' : b.beta with
          | none => simp [affine, za, zb, hr'] at h
          | some r =>
            cases hA : a.affine with
            | error e => simp [affine, za, zb, hr', hA] at h
            | ok q =>
              simp [affine, za, zb, hr', hA] at h
              subst h
              simp only [Term.eval, ← b.beta_correct r hr' env rates, ha q hA hrate]
              cases hq : q.remainder with
              | none =>
                  cases hv : r.eval env <;> simp [Affine.value, hq, plusRight, hv]
              | some l =>
                  cases hv : r.eval env <;> cases hw : l.eval env <;>
                    simp [Affine.value, hq, plusRight, NamedExpr.eval, hv, hw]
                  ring
        · simp [affine, za, zb] at h
  | mul a b ha hb =>
      cases hla : a.literal with
      | some c =>
          cases hB : b.affine with
          | error e => simp [affine, hla, hB, Bind.bind, Except.bind] at h
          | ok q =>
            cases hq : q.remainder with
            | some _ => simp [affine, hla, hB, hq, Bind.bind, Except.bind] at h
            | none =>
              simp [affine, hla, hB, hq, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
              subst h
              simp only [Term.eval, a.literal_correct c hla, hb q hB hrate]
              simp [Affine.value, hq]
              ring
      | none =>
          cases hlb : b.literal with
          | none => simp [affine, hla, hlb] at h
          | some c =>
            cases hA : a.affine with
            | error e => simp [affine, hla, hlb, hA, Bind.bind, Except.bind] at h
            | ok q =>
              cases hq : q.remainder with
              | some _ => simp [affine, hla, hlb, hA, hq, Bind.bind, Except.bind] at h
              | none =>
                simp [affine, hla, hlb, hA, hq, Bind.bind, Except.bind, Pure.pure,
                  Except.pure] at h
                subst h
                simp only [Term.eval, b.literal_correct c hlb, ha q hA hrate]
                simp [Affine.value, hq]
                ring

/-- `(opposite - remainder) / scale`, written without a unit factor. -/
def solution (scale : ℚ) (opposite : NamedExpr) (remainder : Option NamedExpr) :
    NamedExpr :=
  let difference := match remainder with
    | none => opposite
    | some r => .add opposite (.neg r)
  if scale = 1 then difference else .mul (.constant scale⁻¹) difference

/-- A successful isolation keeps the sides it read and the facts it checked. -/
structure Isolated (c : Context) (output : String) (lhs rhs : Term) where
  side : Term
  opposite : Term
  sides : (side = lhs ∧ opposite = rhs) ∨ (side = rhs ∧ opposite = lhs)
  affine : Affine
  recognized : side.affine = .ok affine
  axis : affine.axis = c.axis
  located : c.locate affine.state = some output
  nonzero : affine.scale ≠ 0
  other : NamedExpr
  normalized : opposite.beta = some other

def Isolated.expr {c : Context} {output : String} {lhs rhs : Term}
    (i : Isolated c output lhs rhs) : NamedExpr :=
  solution i.affine.scale i.other i.affine.remainder

private def orient (lhs rhs : Term) :
    Except ErrorCode {sides : Term × Term //
      (sides.1 = lhs ∧ sides.2 = rhs) ∨ (sides.1 = rhs ∧ sides.2 = lhs)} :=
  match lhs.derivatives, rhs.derivatives with
  | 0, 0 => .error .missingDerivative
  | 1, 0 => .ok ⟨(lhs, rhs), .inl ⟨rfl, rfl⟩⟩
  | 0, 1 => .ok ⟨(rhs, lhs), .inr ⟨rfl, rfl⟩⟩
  | 0, _ | _, 0 => .error .repeatedDerivative
  | _, _ => .error .competingDerivative

/-- Isolate the derivative of the state whose derivative port is `output`. -/
def isolate (c : Context) (output : String) (lhs rhs : Term) :
    Except ErrorCode (Isolated c output lhs rhs) := do
  lhs.checkDerivatives c
  rhs.checkDerivatives c
  let ⟨(side, opposite), sides⟩ ← orient lhs rhs
  match hp : side.affine with
  | .error e => .error e
  | .ok p =>
    if ha : p.axis = c.axis then
      if hl : c.locate p.state = some output then
        if hs : p.scale = 0 then .error .zeroScale
        else
          match ho : opposite.beta with
          | none => .error .unsupportedDerivative
          | some o => .ok ⟨side, opposite, sides, p, hp, ha, hl, hs, o, ho⟩
      else .error .missingDerivative
    else .error .mixedDerivative

private theorem solve_scaled (q w y z : ℝ) (hq : q ≠ 0) :
    z = q * w + y ↔ q⁻¹ * (z + -y) = w := by
  constructor
  · intro h; rw [h]; field_simp; ring
  · intro h; rw [← h]; field_simp; ring

/-- The isolated right-hand side is `(opposite - remainder) / scale`. -/
theorem solution_eval (q : ℚ) (o : NamedExpr) (r : Option NamedExpr)
    (env : String → Option ℝ) :
    (solution q o r).eval env =
      (match r with
        | none => o.eval env
        | some r => do return (← o.eval env) + -(← r.eval env)).map (fun d => (q : ℝ)⁻¹ * d) := by
  unfold solution
  cases r with
  | none =>
      cases h : o.eval env <;> by_cases h1 : q = 1 <;> simp [h1, NamedExpr.eval, h]
  | some r =>
      cases h : o.eval env <;> cases h' : r.eval env <;> by_cases h1 : q = 1 <;>
        simp [h1, NamedExpr.eval, h, h']

/-- Isolation preserves the equation exactly, for every environment, once the
atom is read as the value of the derivative port. -/
theorem Isolated.correct {c : Context} {output : String} {lhs rhs : Term}
    (i : Isolated c output lhs rhs) (env : String → Option ℝ) :
    (env output ≠ none ∧ ∃ v, lhs.eval env (c.rates env) = some v ∧
        rhs.eval env (c.rates env) = some v) ↔
      (env output ≠ none ∧ i.expr.eval env = env output) := by
  cases hw : env output with
  | none => simp
  | some w =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    have hrate : c.rates env i.affine.axis i.affine.state = some w := by
      simp [Context.rates, i.axis, i.located, hw]
    have hside := i.side.affine_correct i.affine i.recognized env (c.rates env) w hrate
    have hopp := i.opposite.beta_correct i.other i.normalized env (c.rates env)
    have hq : (i.affine.scale : ℝ) ≠ 0 := by exact_mod_cast i.nonzero
    have key : (∃ v, i.side.eval env (c.rates env) = some v ∧
        i.opposite.eval env (c.rates env) = some v) ↔ i.expr.eval env = some w := by
      rw [hside, ← hopp, Isolated.expr, solution_eval]
      cases hr : i.affine.remainder with
      | none =>
          cases ho : i.other.eval env with
          | none => simp
          | some z =>
              have := solve_scaled i.affine.scale w 0 z hq
              simp only [add_zero, neg_zero] at this
              simp [Affine.value, hr, this]
      | some r =>
          cases ho : i.other.eval env with
          | none => simp [Affine.value, hr]
          | some z =>
            cases hv : r.eval env with
            | none => simp [Affine.value, hr, hv]
            | some y => simp [Affine.value, hr, hv, solve_scaled _ w y z hq]
    rcases i.sides with ⟨hs, ho⟩ | ⟨hs, ho⟩
    · rw [hs, ho] at key; exact key
    · rw [hs, ho] at key
      rw [← key]
      constructor <;> rintro ⟨v, h1, h2⟩ <;> exact ⟨v, h2, h1⟩

#print axioms Term.affine_correct
#print axioms Isolated.correct
end Gimle.Asgard.Model
