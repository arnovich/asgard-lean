import Gimle.Asgard.Model.Term

/-! Bounded affine differential isolation, with declared velocity states for
higher-order chains.

One source equation `lhs = rhs` in which exactly one side contains exactly one
derivative atom, of the form `q*D_t(x) + r = rhs`, once every other atom whose
state has a declared velocity is read as that velocity (below). The scale `q` is
an exact nonzero signed literal product and `r` and `rhs` are then
derivative-free polynomial terms, with applied lambdas allowed. It is isolated to
`D_t(x) = (rhs - r)/q` with every residual term retained: nothing is
cancelled, integrated or dropped.

The atom is replaced by the declared derivative port of `x`; the equation is
then an ordinary assignment to that port. The axis, start and initial values
are not touched by this pass. They stay in the unchanged `Evolution`, and the
initialized feedback of `Model.Continuous` closes the result. Integrals are
removed before this pass by the inverse rewrites of `Model.Integral`, each of
which keeps its boundary term, or read as declared integral states; an integral
that reaches isolation is rejected.

A higher-order chain `D_t(D_t(x))` is first collapsed to `D_t(v)`, where `v` is
the state declared as the velocity of `x` (`Context.velocity`); longer chains
climb one declared velocity per level. The collapse is exact by the chain
reading of `Context.rates` (`Term.collapse_eval`), and nothing is inferred from
names: a chain with an undeclared level is not collapsed and is rejected.

Every other evolution-axis atom, such as the lower-order `D_t(x)` in
`D_t(D_t(x)) + c*D_t(x) + k*x = 0`, is read as the declared velocity of its state
when it has one (`Term.readVelocities`). Unlike the collapse, that reading is exact only where
the velocity equations hold (`Term.readVelocities_eval`); `SourceBody.lower`
discharges them for the whole system. An atom whose state has no declared
velocity stays a second atom and is rejected.

Rejected, each with its own diagnostic, never as a claim of unsatisfiability:
zero scale, competing atoms on both sides and repeated atoms on one side (those
not read as declared velocities),
non-literal or nonlinear factors, a scale around a sum, higher-order chains
without declared velocities, mixed-axis and non-state derivatives, derivatives
inside lambda applications, and
integrals that no inverse rewrite removed and no declared integral state reads
(`unsupportedIntegral`). An explicit assignment is not isolated; its atoms are read
as declared velocities, and an atom that is not read is rejected. -/
namespace Gimle.Asgard.Model
open Polynomial

/-- What an evolution declaration tells the integral rewrites of
`Model.Integral`: `input` holds for a name read from a state coordinate or a
bound parameter, and `initial x` is the declared initial value of `x` when the
first input named `x` is a state: its value at the declared start.
`integral X` is the state declared as the integral of `X` over the evolution
axis from the start, which the rewrites read in place of `I_t(X)`; a trajectory
must make it the antiderivative of `X` vanishing at the start
(`Trajectory.Regular.integral`). `parameter` holds for a name read from a bound
parameter, whose value a trajectory keeps constant (`Trajectory.Regular.parameter`). -/
structure Boundary where
  input : String → Bool
  initial : String → Option ℚ
  integral : Term → Option String := fun _ => none
  parameter : String → Bool := fun _ => false

/-- `axis` is the evolution axis display name; `locate` maps a state display
name to the display name of its declared derivative port, and `velocity` maps
a state display name to the name declared as its first derivative (checked to
be a state by `SourceBody.VelocityStates`). `boundary` is present only for an
evolution declaration; without it no integral is rewritten. -/
structure Context where
  axis : String
  locate : String → Option String
  velocity : String → Option String
  boundary : Option Boundary := none

/-- The state reached from `x` through `k` declared velocities. -/
def Context.lift (c : Context) : Nat → String → Option String
  | 0, x => some x
  | k + 1, x => (c.lift k x).bind c.velocity

/-- `D_t(x)` denotes the value of `x`'s derivative port, and nothing on
another axis. A chain of `k + 1` evolution derivatives of `x` denotes the
derivative port of the state `k` declared velocities above `x`: `D_t(D_t(x))`
is `D_t(v)` when `v` is declared as the velocity of `x`. `SourceBody.Solves`
ties each port to the actual derivative and each velocity to its state's
derivative, so the chain denotes the iterated derivative
(`SourceBody.Solves.chain_denotes`). -/
def Context.rates {α : Type} (c : Context) (env : String → Option α) :
    List String → String → Option α :=
  fun axes state => if axes ≠ [] ∧ axes.all (· == c.axis) then
    ((c.lift (axes.length - 1) state).bind c.locate).bind env else none

/-- A context with no derivatives: every atom is rejected by isolation. -/
def Context.empty : Context := ⟨"", fun _ => none, fun _ => none, none⟩

/-- Collapse every evolution-axis chain whose levels all have declared
velocities to one atom `D_t(top)`. Lambda applications are left untouched: a
derivative inside one is rejected later. That is also why `collapse_eval` holds:
a binder masks only a chain's base name in `Term.eval`, not the velocities it
climbs, so under a binder named like a velocity the collapsed atom would read
differently. -/
def Term.collapse (c : Context) : Term → Term
  | .add a b => .add (a.collapse c) (b.collapse c)
  | .mul a b => .mul (a.collapse c) (b.collapse c)
  | .neg a => .neg (a.collapse c)
  | .derivative axis operand =>
      match operand.chain with
      | some (axes, state) =>
          if axes ≠ [] ∧ (axis :: axes).all (· == c.axis) then
            match c.lift axes.length state with
            | some top => .derivative axis (.var top)
            | none => .derivative axis operand
          else .derivative axis operand
      | none => .derivative axis operand
  | t => t

/-- Collapsing preserves meaning exactly in every environment, under the
chain reading of the same context. -/
theorem Term.collapse_eval (c : Context) (t : Term) (env : String → Option ℝ)
    (atoms : Term → Option ℝ) :
    (t.collapse c).eval env (c.rates env) atoms = t.eval env (c.rates env) atoms := by
  induction t with
  | var _ | constant _ | apply _ _ _ | integral _ _ _ => rfl
  | add a b ha hb => simp only [collapse, Term.eval, ha, hb]
  | mul a b ha hb => simp only [collapse, Term.eval, ha, hb]
  | neg a ha => simp only [collapse, Term.eval, ha]
  | derivative axis operand _ =>
      cases hc : operand.chain with
      | none => simp [collapse, hc]
      | some p =>
        obtain ⟨axes, state⟩ := p
        by_cases h : axes ≠ [] ∧ (axis :: axes).all (· == c.axis) = true
        · cases hl : c.lift axes.length state with
          | none => simp only [collapse, hc, if_pos h, hl]
          | some top =>
            simp only [collapse, hc, if_pos h, hl]
            obtain ⟨hne, hall⟩ := h
            have hall' := hall
            simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall'
            simp only [Term.eval, Term.chain, Context.rates, hc]
            rw [if_pos ⟨List.cons_ne_nil _ _, by simp [hall'.1]⟩,
              if_pos ⟨List.cons_ne_nil _ _, hall⟩]
            simp [Context.lift, hl]
        · simp only [collapse, hc, if_neg h]

/-- The velocity equations of a context, read through derivative ports: in
`env`, each declared velocity `y` of a state `x` carries the value of `x`'s
derivative port. `Term.readVelocities` is exact only where this holds;
`SourceBody.lower` discharges it for the whole system, because every velocity
declaration is itself one of the source equations. -/
def Context.VelocitiesHold (c : Context) (env : String → Option ℝ) : Prop :=
  ∀ x y, c.velocity x = some y → (c.locate x).bind env = env y

/-- Read every atom other than the one defining `output` as the velocity
declared for it. After `collapse`, each declared chain is one atom `D_t(y)`; an
evolution-axis atom `D_t(y)` of a state `y` whose derivative port is not
`output`, and which has a declared velocity `z`, becomes `z`. The atom defining
`output` is kept, as is every other atom, so an undeclared one is left for the
caller to reject: isolation in a differential, beta normalization in an explicit
assignment, whose `output` is its own output port. Lambda applications are left
untouched, as in `collapse`: a binder named like the velocity would capture the
name substituted for the atom. -/
def Term.readVelocities (c : Context) (output : String) : Term → Term
  | .add a b => .add (a.readVelocities c output) (b.readVelocities c output)
  | .mul a b => .mul (a.readVelocities c output) (b.readVelocities c output)
  | .neg a => .neg (a.readVelocities c output)
  | .derivative axis operand =>
      match operand with
      | .var y =>
          if axis = c.axis ∧ (c.locate y).isSome ∧ c.locate y ≠ some output then
            match c.velocity y with
            | some z => .var z
            | none => .derivative axis operand
          else .derivative axis operand
      | _ => .derivative axis operand
  | t => t

/-- Reading lower-order atoms as velocities preserves meaning wherever the
velocity equations hold. Unlike `collapse_eval`, this needs the premise: in an
arbitrary environment the derivative port of `y` and its velocity are unrelated. -/
theorem Term.readVelocities_eval (c : Context) (output : String) (t : Term)
    (env : String → Option ℝ) (atoms : Term → Option ℝ) (h : c.VelocitiesHold env) :
    (t.readVelocities c output).eval env (c.rates env) atoms =
      t.eval env (c.rates env) atoms := by
  induction t with
  | var _ | constant _ | apply _ _ _ | integral _ _ _ => rfl
  | add a b ha hb => simp only [readVelocities, Term.eval, ha, hb]
  | mul a b ha hb => simp only [readVelocities, Term.eval, ha, hb]
  | neg a ha => simp only [readVelocities, Term.eval, ha]
  | derivative axis operand _ =>
      cases operand with
      | var y =>
          by_cases hc : axis = c.axis ∧ (c.locate y).isSome ∧ c.locate y ≠ some output
          · cases hv : c.velocity y with
            | none => simp only [readVelocities, if_pos hc, hv]
            | some z =>
                simp only [readVelocities, if_pos hc, hv, Term.eval, Term.chain]
                rw [← h y z hv]
                simp [Context.rates, Context.lift, hc.1]
          · simp only [readVelocities, if_neg hc]
      | _ => rfl

/-- Read every first-order evolution-axis atom `D_t(y)` of a state `y` as the name
of its derivative port. Unlike `readVelocities`, this is exact in every environment
(`Term.readPorts_eval`): `Context.rates` reads `D_t(y)` as that port's value. The
lowered assignment then refers to the port, which the lowered body defines.
Lambda applications are left untouched. -/
def Term.readPorts (c : Context) : Term → Term
  | .add a b => .add (a.readPorts c) (b.readPorts c)
  | .mul a b => .mul (a.readPorts c) (b.readPorts c)
  | .neg a => .neg (a.readPorts c)
  | .derivative axis (.var y) =>
      if axis = c.axis then
        match c.locate y with
        | some port => .var port
        | none => .derivative axis (.var y)
      else .derivative axis (.var y)
  | t => t

/-- Reading first-order atoms as their ports preserves meaning in every environment. -/
theorem Term.readPorts_eval (c : Context) (t : Term) (env : String → Option ℝ)
    (atoms : Term → Option ℝ) :
    (t.readPorts c).eval env (c.rates env) atoms = t.eval env (c.rates env) atoms := by
  induction t with
  | var _ | constant _ | apply _ _ _ | integral _ _ _ => rfl
  | add a b ha hb => simp only [readPorts, Term.eval, ha, hb]
  | mul a b ha hb => simp only [readPorts, Term.eval, ha, hb]
  | neg a ha => simp only [readPorts, Term.eval, ha]
  | derivative axis operand _ =>
      cases operand with
      | var y =>
          by_cases hc : axis = c.axis
          · cases hl : c.locate y with
            | none => simp only [readPorts, if_pos hc, hl]
            | some port =>
                simp only [readPorts, if_pos hc, hl, Term.eval, Term.chain, Context.rates]
                simp [Context.lift, hc, hl]
          · simp only [readPorts, if_neg hc]
      | _ => rfl

/-- Classify every derivative node, before counting. An integral, anywhere, is
outside this pass. -/
def Term.checkDerivatives (c : Context) : Term → Except ErrorCode Unit
  | .var _ | .constant _ => .ok ()
  | .integral _ _ => .error .unsupportedIntegral
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
      | .integral _ _ => .error .unsupportedIntegral
      | .derivative inner inside =>
          match inside.chain with
          | some (axes, base) =>
              if !(axis :: inner :: axes).all (· == c.axis) then .error .mixedDerivative
              else if (c.locate base).isNone then .error .unsupportedDerivative
              else .error .higherOrderDerivative
          | none =>
              if axis ≠ inner ∨ axis ≠ c.axis then .error .mixedDerivative
              else .error .unsupportedDerivative
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
  | .integral _ _ => .error .unsupportedIntegral
  | .var _ | .constant _ => .error .missingDerivative

theorem Term.affine_correct (t : Term) (p : Affine) (h : t.affine = .ok p)
    (env : String → Option ℝ) (rates : List String → String → Option ℝ)
    (atoms : Term → Option ℝ) (rate : ℝ)
    (hrate : rates [p.axis] p.state = some rate) : t.eval env rates atoms = p.value env rate := by
  induction t generalizing p with
  | var _ | constant _ => simp [affine] at h
  | apply | integral => simp [affine] at h
  | derivative axis operand _ =>
      cases operand <;> simp [affine] at h
      subst h
      simpa [Term.eval, Term.chain, Affine.value] using hrate
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
            simp only [Term.eval, ← a.beta_correct l hl env rates atoms, hb q hB hrate]
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
              simp only [Term.eval, ← b.beta_correct r hr' env rates atoms, ha q hA hrate]
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
              simp only [Term.eval, a.literal_correct c hla env rates atoms, hb q hB hrate]
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
                simp only [Term.eval, b.literal_correct c hlb env rates atoms, ha q hA hrate]
                simp [Affine.value, hq]
                ring

/-- `(opposite - remainder) / scale`, written without a unit factor. -/
def isolatedRhs (scale : ℚ) (opposite : NamedExpr) (remainder : Option NamedExpr) :
    NamedExpr :=
  let difference := match remainder with
    | none => opposite
    | some r => .add opposite (.neg r)
  if scale = 1 then difference else .mul (.constant scale⁻¹) difference

/-- A successful isolation keeps the collapsed sides it read and the facts it
checked. -/
structure Isolated (c : Context) (output : String) (lhs rhs : Term) where
  side : Term
  opposite : Term
  sides : (side = lhs.collapse c ∧ opposite = rhs.collapse c) ∨
    (side = rhs.collapse c ∧ opposite = lhs.collapse c)
  affine : Affine
  recognized : side.affine = .ok affine
  axis : affine.axis = c.axis
  located : c.locate affine.state = some output
  nonzero : affine.scale ≠ 0
  other : NamedExpr
  normalized : opposite.beta = some other

def Isolated.expr {c : Context} {output : String} {lhs rhs : Term}
    (i : Isolated c output lhs rhs) : NamedExpr :=
  isolatedRhs i.affine.scale i.other i.affine.remainder

private def orient (lhs rhs : Term) :
    Except ErrorCode {sides : Term × Term //
      (sides.1 = lhs ∧ sides.2 = rhs) ∨ (sides.1 = rhs ∧ sides.2 = lhs)} :=
  match lhs.derivatives, rhs.derivatives with
  | 0, 0 => .error .missingDerivative
  | 1, 0 => .ok ⟨(lhs, rhs), .inl ⟨rfl, rfl⟩⟩
  | 0, 1 => .ok ⟨(rhs, lhs), .inr ⟨rfl, rfl⟩⟩
  | 0, _ | _, 0 => .error .repeatedDerivative
  | _, _ => .error .competingDerivative

/-- Isolate the derivative of the state whose derivative port is `output`,
after collapsing declared higher-order chains. -/
def isolate (c : Context) (output : String) (lhs rhs : Term) :
    Except ErrorCode (Isolated c output lhs rhs) := do
  (lhs.collapse c).checkDerivatives c
  (rhs.collapse c).checkDerivatives c
  let ⟨(side, opposite), sides⟩ ← orient (lhs.collapse c) (rhs.collapse c)
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
theorem isolatedRhs_eval (q : ℚ) (o : NamedExpr) (r : Option NamedExpr)
    (env : String → Option ℝ) :
    (isolatedRhs q o r).eval env =
      (match r with
        | none => o.eval env
        | some r => do return (← o.eval env) + -(← r.eval env)).map (fun d => (q : ℝ)⁻¹ * d) := by
  unfold isolatedRhs
  cases r with
  | none =>
      cases h : o.eval env <;> by_cases h1 : q = 1 <;> simp [h1, NamedExpr.eval, h]
  | some r =>
      cases h : o.eval env <;> cases h' : r.eval env <;> by_cases h1 : q = 1 <;>
        simp [h1, NamedExpr.eval, h, h']

/-- Isolation preserves the equation exactly, for every environment, once the
atom is read as the value of the derivative port. -/
theorem Isolated.correct {c : Context} {output : String} {lhs rhs : Term}
    (i : Isolated c output lhs rhs) (env : String → Option ℝ) (atoms : Term → Option ℝ) :
    (env output ≠ none ∧ ∃ v, lhs.eval env (c.rates env) atoms = some v ∧
        rhs.eval env (c.rates env) atoms = some v) ↔
      (env output ≠ none ∧ i.expr.eval env = env output) := by
  cases hw : env output with
  | none => simp
  | some w =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    have hrate : c.rates env [i.affine.axis] i.affine.state = some w := by
      simp [Context.rates, Context.lift, i.axis, i.located, hw]
    have hside := i.side.affine_correct i.affine i.recognized env (c.rates env) atoms w hrate
    have hopp := i.opposite.beta_correct i.other i.normalized env (c.rates env) atoms
    have hq : (i.affine.scale : ℝ) ≠ 0 := by exact_mod_cast i.nonzero
    have key : (∃ v, i.side.eval env (c.rates env) atoms = some v ∧
        i.opposite.eval env (c.rates env) atoms = some v) ↔ i.expr.eval env = some w := by
      rw [hside, ← hopp, Isolated.expr, isolatedRhs_eval]
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
    · rw [hs, ho, lhs.collapse_eval, rhs.collapse_eval] at key; exact key
    · rw [hs, ho, lhs.collapse_eval, rhs.collapse_eval] at key
      rw [← key]
      constructor <;> rintro ⟨v, h1, h2⟩ <;> exact ⟨v, h2, h1⟩

#print axioms Term.collapse_eval
#print axioms Term.readVelocities_eval
#print axioms Term.readPorts_eval
#print axioms Term.affine_correct
#print axioms Isolated.correct
end Gimle.Asgard.Model
