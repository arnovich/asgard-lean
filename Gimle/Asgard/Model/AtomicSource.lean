import Gimle.Asgard.Model.Source
import Gimle.Asgard.RealAtomics.Feedback

/-! Source declarations with real atomics and partial division, compiled to
`RealAtomics` circuits with every domain kept.

A source term may apply a `RealAtomics` operation (`Term.unary`, `Term.binary`):
`sqrt`, `log`, `exp`, the trigonometric and hyperbolic functions, real powers and
division by an expression. `Term.eval` gives such a node a value only inside its
domain, strictly in every child, so the unchanged source relation
`SourceBody.Solves` (and `SourceBody.Observes`) already carries the complete
`Defined` predicate of every equation, including unused assignments and domains
under a zero multiplier. This module lowers such a body and compiles it without
dropping any of those conditions:

- explicit assignments and the derivative-free residuals of differential
  equations are beta-normalized to `PartialExpr`, named partial expressions over
  the `RealAtomics` operations (`Term.betaPartial`);
- a differential equation is isolated as in `Model.Differential`
  (`isolatePartial`): the scale is still an exact nonzero literal, possibly a
  quotient of literal products, and a derivative under an atomic or in a
  denominator is rejected (`atomicDerivative`);
- assignments are resolved to coordinate `RealAtomics.Expr`s by the same
  proof-carrying scheduling as `Model.Resolution` (`PartialTrace`), with
  parameters specialized to exact constants;
- the compiled circuit (`guardedField`) evaluates the selected outputs **and**
  every resolved assignment, and discards the latter, so its operational
  relation requires every assignment to be `Defined`
  (`guardedField_defined`).

A polynomial declaration is related to that circuit's `Rel`
(`AtomicPolynomialModel.correct`). A continuous one is related to the
partial-field feedback of `RealAtomics.Feedback`, whose relation requires the
field to be `Defined` along the state at every time of the forward domain
(`AtomicContinuousModel.solves_iff_closes`, `AtomicContinuousModel.solves_iff`);
the total `Dynamics.close` is not used, since it would drop those conditions.

Out of scope here, and rejected with a diagnostic: integrals and integral
declarations (`unsupportedIntegral`), observations of a continuous declaration,
drivers, and a derivative anywhere under an atomic or a non-literal division,
even one that `Term.readVelocities` would read at top level. The `Laws.lean`
rewrites are not applied: nothing is simplified, so `log(exp(x))` keeps both
nodes, and `0 * log(x)` keeps the domain of `log`. -/
namespace Gimle.Asgard.RealAtomics

@[simp] theorem Unary.partial_neg (x : ℝ) : Unary.neg.partial x = some (-x) :=
  Unary.partial_of_domain trivial

@[simp] theorem Binary.partial_add (x y : ℝ) : Binary.add.partial x y = some (x + y) :=
  Binary.partial_of_domain trivial

@[simp] theorem Binary.partial_mul (x y : ℝ) : Binary.mul.partial x y = some (x * y) :=
  Binary.partial_of_domain trivial

/-- The value where `Defined`, and nothing elsewhere. -/
noncomputable def Expr.partialValue {k n : Nat} (axes : Point k) (x : Point n) :
    Expr k n → Option ℝ
  | .input i => some (x i)
  | .constant q => some q
  | .unary op e => (e.partialValue axes x).bind op.partial
  | .binary op a b => do op.partial (← a.partialValue axes x) (← b.partialValue axes x)
  | .generated op axis => op.partial (axes axis)

/-- A partial value is exactly a defined point and its value. -/
theorem Expr.partialValue_eq_some {k n : Nat} (e : Expr k n) (axes : Point k) (x : Point n)
    (v : ℝ) : e.partialValue axes x = some v ↔ e.Defined axes x ∧ e.value axes x = v := by
  induction e generalizing v with
  | input i => simp [partialValue, Defined, value]
  | constant q => simp [partialValue, Defined, value]
  | unary op e ih =>
      cases h : e.partialValue axes x with
      | none =>
          simp only [partialValue, h, Option.bind_none, reduceCtorEq, false_iff, Defined,
            not_and]
          intro hd
          have := (ih (e.value axes x)).mpr ⟨hd.1, rfl⟩
          rw [h] at this
          cases this
      | some w =>
          obtain ⟨hd, rfl⟩ := (ih w).mp h
          simp [partialValue, h, Defined, value, hd, Unary.partial_eq_some]
  | binary op a b iha ihb =>
      cases ha : a.partialValue axes x with
      | none =>
          simp only [partialValue, ha, Option.bind_eq_bind, Option.bind_none, reduceCtorEq,
            false_iff, Defined, not_and]
          intro hd
          have := (iha (a.value axes x)).mpr ⟨hd.1.1, rfl⟩
          rw [ha] at this
          cases this
      | some va =>
        cases hb : b.partialValue axes x with
        | none =>
            simp only [partialValue, ha, hb, Option.bind_eq_bind, Option.bind_some,
              Option.bind_none, reduceCtorEq, false_iff, Defined, not_and]
            intro hd
            have := (ihb (b.value axes x)).mpr ⟨hd.1.2, rfl⟩
            rw [hb] at this
            cases this
        | some vb =>
            obtain ⟨hda, rfl⟩ := (iha va).mp ha
            obtain ⟨hdb, rfl⟩ := (ihb vb).mp hb
            simp [partialValue, ha, hb, Defined, value, hda, hdb, Binary.partial_eq_some]
  | generated op axis => simp [partialValue, Defined, value, Unary.partial_eq_some]

/-- Every coordinate of `outs`, evaluated together with every `guards`
expression, which is then discarded. The discarded expressions still have to be
`Defined` (`guardedField_defined`): this is how an unused assignment keeps its
domain in a compiled circuit. -/
def guardedField {k n m r : Nat} (outs : Fin m → Expr k n) (guards : Fin r → Expr k n) :
    Circuit k n m :=
  .compose (vectorField (Fin.addCases outs guards)) (.embed (Polynomial.route (Fin.castAdd r)))

@[simp] theorem guardedField_value {k n m r : Nat} (outs : Fin m → Expr k n)
    (guards : Fin r → Expr k n) (axes : Point k) (x : Point n) :
    (guardedField outs guards).value axes x = fun i => (outs i).value axes x := by
  funext i
  simp [guardedField, Circuit.value]

@[simp] theorem guardedField_defined {k n m r : Nat} (outs : Fin m → Expr k n)
    (guards : Fin r → Expr k n) (axes : Point k) (x : Point n) :
    (guardedField outs guards).Defined axes x ↔
      (∀ i, (outs i).Defined axes x) ∧ ∀ j, (guards j).Defined axes x := by
  simp only [guardedField, Circuit.Defined, vectorField_defined, and_true]
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castAdd r i), fun j => by simpa using h (Fin.natAdd m j)⟩
  · rintro ⟨ho, hg⟩ i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · simpa using ho i
    · simpa using hg j

/-- The operational relation of a guarded field: every output and every guard is
`Defined`, and the outputs are their values. -/
theorem guardedField_rel {k n m r : Nat} (outs : Fin m → Expr k n)
    (guards : Fin r → Expr k n) (axes : Point k) (x : Point n) (y : Point m) :
    (guardedField outs guards).Rel axes x y ↔
      ((∀ i, (outs i).Defined axes x) ∧ ∀ j, (guards j).Defined axes x) ∧
        y = fun i => (outs i).value axes x := by
  rw [Circuit.rel_iff, guardedField_defined, guardedField_value]

end Gimle.Asgard.RealAtomics

namespace Gimle.Asgard.Model
open Polynomial

/-! ## Named partial expressions -/

/-- A named expression over the `RealAtomics` operations; addition,
multiplication and negation are the total `RealAtomics` operations. -/
inductive PartialExpr where
  | var (name : String)
  | constant (value : ℚ)
  | unary (op : RealAtomics.Unary) (argument : PartialExpr)
  | binary (op : RealAtomics.Binary) (left right : PartialExpr)
  deriving Repr, DecidableEq

/-- Independent semantics: a partial node has a value only inside its domain,
strictly in every child. -/
noncomputable def PartialExpr.eval (env : String → Option ℝ) : PartialExpr → Option ℝ
  | .var name => env name
  | .constant q => some q
  | .unary op a => (a.eval env).bind op.partial
  | .binary op a b => do op.partial (← a.eval env) (← b.eval env)

/-- Capture-free substitution: a `PartialExpr` has no binders. -/
def PartialExpr.subst (e : PartialExpr) (name : String) (value : PartialExpr) : PartialExpr :=
  match e with
  | .var n => if n = name then value else .var n
  | .constant q => .constant q
  | .unary op a => .unary op (a.subst name value)
  | .binary op a b => .binary op (a.subst name value) (b.subst name value)

theorem PartialExpr.subst_eval (e : PartialExpr) (name : String) (value : PartialExpr)
    (env : String → Option ℝ) :
    (e.subst name value).eval env = e.eval (rebind env name (value.eval env)) := by
  induction e with
  | var n => by_cases h : n = name <;> simp [PartialExpr.subst, PartialExpr.eval, rebind, h]
  | constant q => rfl
  | unary op a ha => simp only [PartialExpr.subst, PartialExpr.eval, ha]
  | binary op a b ha hb => simp only [PartialExpr.subst, PartialExpr.eval, ha, hb]

/-- Scoped beta normalization that keeps real atomics and partial binary
operations, as `Term.beta` keeps polynomial nodes. A derivative or an integral
anywhere returns `none`. -/
def Term.betaPartial : Term → Option PartialExpr
  | .var name => some (.var name)
  | .constant q => some (.constant q)
  | .add a b => do return .binary .add (← a.betaPartial) (← b.betaPartial)
  | .mul a b => do return .binary .mul (← a.betaPartial) (← b.betaPartial)
  | .neg a => do return .unary .neg (← a.betaPartial)
  | .apply x body arg => do return (← body.betaPartial).subst x (← arg.betaPartial)
  | .unary op a => do return .unary op (← a.betaPartial)
  | .binary op a b => do return .binary op (← a.betaPartial) (← b.betaPartial)
  | .derivative _ _ | .integral _ _ => none

/-- Beta normalization with atomics preserves meaning exactly, domains included,
for every environment and whatever derivative or atom interpretation. -/
theorem Term.betaPartial_correct (t : Term) (e : PartialExpr) (h : t.betaPartial = some e)
    (env : String → Option ℝ) (rates : List String → String → Option ℝ)
    (atoms : Term → Option ℝ) :
    e.eval env = t.eval env rates atoms := by
  induction t generalizing e env rates atoms with
  | var name => cases h; rfl
  | constant q => cases h; rfl
  | add a b ha hb =>
      cases hA : a.betaPartial <;> cases hB : b.betaPartial <;> simp [betaPartial, hA, hB] at h
      subst h
      simp only [PartialExpr.eval, Term.eval, ha _ hA env rates atoms, hb _ hB env rates atoms]
      cases a.eval env rates atoms <;> cases b.eval env rates atoms <;> simp
  | mul a b ha hb =>
      cases hA : a.betaPartial <;> cases hB : b.betaPartial <;> simp [betaPartial, hA, hB] at h
      subst h
      simp only [PartialExpr.eval, Term.eval, ha _ hA env rates atoms, hb _ hB env rates atoms]
      cases a.eval env rates atoms <;> cases b.eval env rates atoms <;> simp
  | neg a ha =>
      cases hA : a.betaPartial <;> simp [betaPartial, hA] at h
      subst h
      simp only [PartialExpr.eval, Term.eval, ha _ hA env rates atoms]
      cases a.eval env rates atoms <;> simp
  | apply x body arg hbody harg =>
      cases hB : body.betaPartial <;> cases hA : arg.betaPartial <;>
        simp [betaPartial, hB, hA] at h
      subst h
      rw [PartialExpr.subst_eval, Term.eval, hbody _ hB, harg _ hA env rates atoms]
  | unary op a ha =>
      cases hA : a.betaPartial <;> simp [betaPartial, hA] at h
      subst h
      simp only [PartialExpr.eval, Term.eval, ha _ hA env rates atoms]
  | binary op a b ha hb =>
      cases hA : a.betaPartial <;> cases hB : b.betaPartial <;> simp [betaPartial, hA, hB] at h
      subst h
      simp only [PartialExpr.eval, Term.eval, ha _ hA env rates atoms, hb _ hB env rates atoms]
  | derivative axis operand _ => simp [betaPartial] at h
  | integral axis operand _ => simp [betaPartial] at h

/-! ## Isolation with partial residuals

`Term.affine` and `isolate` of `Model.Differential`, with residuals normalized by
`Term.betaPartial` rather than `Term.beta`. The accepted scales, the checks and
the diagnostics are the same: `Term.checkDerivatives` runs first, so a
derivative under an atomic or in a denominator is `atomicDerivative`, and a
division of the atom by a non-literal is `nonlinearDerivative`. -/

/-- One side, read as `scale * D_axis(state) + remainder`, the remainder being a
partial expression; `none` means no remainder term was written. -/
structure PartialAffine where
  axis : String
  state : String
  scale : ℚ
  remainder : Option PartialExpr

noncomputable def PartialAffine.value (p : PartialAffine) (env : String → Option ℝ)
    (rate : ℝ) : Option ℝ :=
  match p.remainder with
  | none => some (p.scale * rate)
  | some r => (r.eval env).map (fun y => p.scale * rate + y)

private def plusLeft (l : PartialExpr) : Option PartialExpr → PartialExpr
  | none => l
  | some r => .binary .add l r

private def plusRight (r : PartialExpr) : Option PartialExpr → PartialExpr
  | none => r
  | some l => .binary .add l r

/-- `Term.affine`, with derivative-free terms normalized by `Term.betaPartial`. -/
def Term.partialAffine : Term → Except ErrorCode PartialAffine
  | .derivative axis operand =>
      match operand with
      | .var state => .ok ⟨axis, state, 1, none⟩
      | .derivative _ _ => .error .higherOrderDerivative
      | _ => .error .unsupportedDerivative
  | .neg a => do
      let p ← a.partialAffine
      return ⟨p.axis, p.state, -p.scale, p.remainder.map (.unary .neg)⟩
  | .add a b =>
      if a.derivatives = 0 then
        match a.betaPartial with
        | none => .error .unsupportedDerivative
        | some l => do
            let p ← b.partialAffine
            return ⟨p.axis, p.state, p.scale, some (plusLeft l p.remainder)⟩
      else if b.derivatives = 0 then
        match b.betaPartial with
        | none => .error .unsupportedDerivative
        | some r => do
            let p ← a.partialAffine
            return ⟨p.axis, p.state, p.scale, some (plusRight r p.remainder)⟩
      else .error .repeatedDerivative
  | .mul a b =>
      match a.literal, b.literal with
      | some c, _ => do
          let p ← b.partialAffine
          if p.remainder.isSome then .error .unsupportedDerivative
          else return ⟨p.axis, p.state, c * p.scale, none⟩
      | none, some c => do
          let p ← a.partialAffine
          if p.remainder.isSome then .error .unsupportedDerivative
          else return ⟨p.axis, p.state, p.scale * c, none⟩
      | none, none => .error .nonlinearDerivative
  | .binary .division a b =>
      match b.literal with
      | some c =>
          if c = 0 then .error .zeroScale
          else do
            let p ← a.partialAffine
            if p.remainder.isSome then .error .unsupportedDerivative
            else return ⟨p.axis, p.state, p.scale / c, none⟩
      | none => .error .nonlinearDerivative
  | .binary _ _ _ | .unary _ _ => .error .atomicDerivative
  | .apply _ _ _ => .error .unsupportedDerivative
  | .integral _ _ => .error .unsupportedIntegral
  | .var _ | .constant _ => .error .missingDerivative

theorem Term.partialAffine_correct (t : Term) (p : PartialAffine) (h : t.partialAffine = .ok p)
    (env : String → Option ℝ) (rates : List String → String → Option ℝ)
    (atoms : Term → Option ℝ) (rate : ℝ)
    (hrate : rates [p.axis] p.state = some rate) : t.eval env rates atoms = p.value env rate := by
  induction t generalizing p with
  | var _ | constant _ => simp [partialAffine] at h
  | apply | integral | unary => simp [partialAffine] at h
  | derivative axis operand _ =>
      cases operand <;> simp [partialAffine] at h
      subst h
      simpa [Term.eval, Term.chain, PartialAffine.value] using hrate
  | neg a ha =>
      cases hA : a.partialAffine with
      | error e => simp [partialAffine, hA] at h
      | ok q =>
          simp [partialAffine, hA] at h
          subst h
          have := ha q hA hrate
          simp only [Term.eval, this, PartialAffine.value]
          cases hr : q.remainder with
          | none => simp
          | some r =>
              cases hv : r.eval env <;> simp [PartialExpr.eval, hv]
              ring
  | add a b ha hb =>
      by_cases za : a.derivatives = 0
      · cases hl : a.betaPartial with
        | none => simp [partialAffine, za, hl] at h
        | some l =>
          cases hB : b.partialAffine with
          | error e => simp [partialAffine, za, hl, hB] at h
          | ok q =>
            simp [partialAffine, za, hl, hB] at h
            subst h
            simp only [Term.eval, ← a.betaPartial_correct l hl env rates atoms, hb q hB hrate]
            cases hr : q.remainder with
            | none =>
                cases hv : l.eval env <;> simp [PartialAffine.value, hr, plusLeft, hv]
                ring
            | some r =>
                cases hv : l.eval env <;> cases hw : r.eval env <;>
                  simp [PartialAffine.value, hr, plusLeft, PartialExpr.eval, hv, hw]
                ring
      · by_cases zb : b.derivatives = 0
        · cases hr' : b.betaPartial with
          | none => simp [partialAffine, za, zb, hr'] at h
          | some r =>
            cases hA : a.partialAffine with
            | error e => simp [partialAffine, za, zb, hr', hA] at h
            | ok q =>
              simp [partialAffine, za, zb, hr', hA] at h
              subst h
              simp only [Term.eval, ← b.betaPartial_correct r hr' env rates atoms,
                ha q hA hrate]
              cases hq : q.remainder with
              | none =>
                  cases hv : r.eval env <;> simp [PartialAffine.value, hq, plusRight, hv]
              | some l =>
                  cases hv : r.eval env <;> cases hw : l.eval env <;>
                    simp [PartialAffine.value, hq, plusRight, PartialExpr.eval, hv, hw]
                  ring
        · simp [partialAffine, za, zb] at h
  | mul a b ha hb =>
      cases hla : a.literal with
      | some c =>
          cases hB : b.partialAffine with
          | error e => simp [partialAffine, hla, hB, Bind.bind, Except.bind] at h
          | ok q =>
            cases hq : q.remainder with
            | some _ => simp [partialAffine, hla, hB, hq, Bind.bind, Except.bind] at h
            | none =>
              simp [partialAffine, hla, hB, hq, Bind.bind, Except.bind, Pure.pure,
                Except.pure] at h
              subst h
              simp only [Term.eval, a.literal_correct c hla env rates atoms, hb q hB hrate]
              simp [PartialAffine.value, hq]
              ring
      | none =>
          cases hlb : b.literal with
          | none => simp [partialAffine, hla, hlb] at h
          | some c =>
            cases hA : a.partialAffine with
            | error e => simp [partialAffine, hla, hlb, hA, Bind.bind, Except.bind] at h
            | ok q =>
              cases hq : q.remainder with
              | some _ => simp [partialAffine, hla, hlb, hA, hq, Bind.bind, Except.bind] at h
              | none =>
                simp [partialAffine, hla, hlb, hA, hq, Bind.bind, Except.bind, Pure.pure,
                  Except.pure] at h
                subst h
                simp only [Term.eval, b.literal_correct c hlb env rates atoms, ha q hA hrate]
                simp [PartialAffine.value, hq]
                ring
  | binary op a b ha hb =>
      cases op <;> simp only [partialAffine, reduceCtorEq] at h
      cases hlb : b.literal with
      | none => simp [hlb] at h
      | some c =>
        by_cases hc : c = 0
        · simp [hlb, hc] at h
        · cases hA : a.partialAffine with
          | error e => simp [hlb, hc, hA, Bind.bind, Except.bind] at h
          | ok q =>
            cases hq : q.remainder with
            | some _ => simp [hlb, hc, hA, hq, Bind.bind, Except.bind] at h
            | none =>
              simp [hlb, hc, hA, hq, Bind.bind, Except.bind, Pure.pure, Except.pure] at h
              subst h
              have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
              simp only [Term.eval, b.literal_correct c hlb env rates atoms, ha q hA hrate]
              simp [PartialAffine.value, hq, RealAtomics.Binary.partial_of_domain
                (show RealAtomics.Binary.division.Domain (q.scale * rate) c from hc'),
                RealAtomics.Binary.value]
              ring

/-- `(opposite - remainder) / scale`, written without a unit factor. -/
def isolatedPartialRhs (scale : ℚ) (opposite : PartialExpr) (remainder : Option PartialExpr) :
    PartialExpr :=
  let difference := match remainder with
    | none => opposite
    | some r => .binary .add opposite (.unary .neg r)
  if scale = 1 then difference else .binary .mul (.constant scale⁻¹) difference

/-- A successful isolation with partial residuals keeps the collapsed sides it read
and the facts it checked. -/
structure PartialIsolated (c : Context) (output : String) (lhs rhs : Term) where
  side : Term
  opposite : Term
  sides : (side = lhs.collapse c ∧ opposite = rhs.collapse c) ∨
    (side = rhs.collapse c ∧ opposite = lhs.collapse c)
  affine : PartialAffine
  recognized : side.partialAffine = .ok affine
  axis : affine.axis = c.axis
  located : c.locate affine.state = some output
  nonzero : affine.scale ≠ 0
  other : PartialExpr
  normalized : opposite.betaPartial = some other

def PartialIsolated.expr {c : Context} {output : String} {lhs rhs : Term}
    (i : PartialIsolated c output lhs rhs) : PartialExpr :=
  isolatedPartialRhs i.affine.scale i.other i.affine.remainder

private def orient (lhs rhs : Term) :
    Except ErrorCode {sides : Term × Term //
      (sides.1 = lhs ∧ sides.2 = rhs) ∨ (sides.1 = rhs ∧ sides.2 = lhs)} :=
  match lhs.derivatives, rhs.derivatives with
  | 0, 0 => .error .missingDerivative
  | 1, 0 => .ok ⟨(lhs, rhs), .inl ⟨rfl, rfl⟩⟩
  | 0, 1 => .ok ⟨(rhs, lhs), .inr ⟨rfl, rfl⟩⟩
  | 0, _ | _, 0 => .error .repeatedDerivative
  | _, _ => .error .competingDerivative

/-- `isolate`, with partial residuals: isolate the derivative of the state whose
derivative port is `output`, after collapsing declared higher-order chains. -/
def isolatePartial (c : Context) (output : String) (lhs rhs : Term) :
    Except ErrorCode (PartialIsolated c output lhs rhs) := do
  (lhs.collapse c).checkDerivatives c
  (rhs.collapse c).checkDerivatives c
  let ⟨(side, opposite), sides⟩ ← orient (lhs.collapse c) (rhs.collapse c)
  match hp : side.partialAffine with
  | .error e => .error e
  | .ok p =>
    if ha : p.axis = c.axis then
      if hl : c.locate p.state = some output then
        if hs : p.scale = 0 then .error .zeroScale
        else
          match ho : opposite.betaPartial with
          | none => .error .unsupportedDerivative
          | some o => .ok ⟨side, opposite, sides, p, hp, ha, hl, hs, o, ho⟩
      else .error .missingDerivative
    else .error .mixedDerivative

private theorem solve_scaled (q w y z : ℝ) (hq : q ≠ 0) :
    z = q * w + y ↔ q⁻¹ * (z + -y) = w := by
  constructor
  · intro h; rw [h]; field_simp; ring
  · intro h; rw [← h]; field_simp; ring

/-- The isolated right-hand side is `(opposite - remainder) / scale`; it has a
value exactly where the opposite side and the remainder have one. -/
theorem isolatedPartialRhs_eval (q : ℚ) (o : PartialExpr) (r : Option PartialExpr)
    (env : String → Option ℝ) :
    (isolatedPartialRhs q o r).eval env =
      (match r with
        | none => o.eval env
        | some r => do return (← o.eval env) + -(← r.eval env)).map
          (fun d => (q : ℝ)⁻¹ * d) := by
  unfold isolatedPartialRhs
  cases r with
  | none =>
      cases h : o.eval env <;> by_cases h1 : q = 1 <;> simp [h1, PartialExpr.eval, h]
  | some r =>
      cases h : o.eval env <;> cases h' : r.eval env <;> by_cases h1 : q = 1 <;>
        simp [h1, PartialExpr.eval, h, h']

/-- Isolation with partial residuals preserves the equation exactly, domains
included, for every environment, once the atom is read as the value of the
derivative port. -/
theorem PartialIsolated.correct {c : Context} {output : String} {lhs rhs : Term}
    (i : PartialIsolated c output lhs rhs) (env : String → Option ℝ)
    (atoms : Term → Option ℝ) :
    (env output ≠ none ∧ ∃ v, lhs.eval env (c.rates env) atoms = some v ∧
        rhs.eval env (c.rates env) atoms = some v) ↔
      (env output ≠ none ∧ i.expr.eval env = env output) := by
  cases hw : env output with
  | none => simp
  | some w =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    have hrate : c.rates env [i.affine.axis] i.affine.state = some w := by
      simp [Context.rates, Context.lift, i.axis, i.located, hw]
    have hside := i.side.partialAffine_correct i.affine i.recognized env (c.rates env) atoms w
      hrate
    have hopp := i.opposite.betaPartial_correct i.other i.normalized env (c.rates env) atoms
    have hq : (i.affine.scale : ℝ) ≠ 0 := by exact_mod_cast i.nonzero
    have key : (∃ v, i.side.eval env (c.rates env) atoms = some v ∧
        i.opposite.eval env (c.rates env) atoms = some v) ↔ i.expr.eval env = some w := by
      rw [hside, ← hopp, PartialIsolated.expr, isolatedPartialRhs_eval]
      cases hr : i.affine.remainder with
      | none =>
          cases ho : i.other.eval env with
          | none => simp
          | some z =>
              have := solve_scaled i.affine.scale w 0 z hq
              simp only [add_zero, neg_zero] at this
              simp [PartialAffine.value, hr, this]
      | some r =>
          cases ho : i.other.eval env with
          | none => simp [PartialAffine.value, hr]
          | some z =>
            cases hv : r.eval env with
            | none => simp [PartialAffine.value, hr, hv]
            | some y => simp [PartialAffine.value, hr, hv, solve_scaled _ w y z hq]
    rcases i.sides with ⟨hs, ho⟩ | ⟨hs, ho⟩
    · rw [hs, ho, lhs.collapse_eval, rhs.collapse_eval] at key; exact key
    · rw [hs, ho, lhs.collapse_eval, rhs.collapse_eval] at key
      rw [← key]
      constructor <;> rintro ⟨v, h1, h2⟩ <;> exact ⟨v, h2, h1⟩

/-! ## Lowering -/

/-- An explicit assignment whose right-hand side is a partial expression. -/
structure PartialAssignment where
  output : Port
  rhs : PartialExpr
  deriving Repr, DecidableEq

/-- Every lowered equation, with a defined output. As in `Model.Resolution`, an
unused assignment, and so its domain, remains a requirement. -/
def PartialEquations (as : List PartialAssignment) (env : String → Option ℝ) : Prop :=
  ∀ a ∈ as, env a.output.name ≠ none ∧ a.rhs.eval env = env a.output.name

theorem partialEquations_append (l r : List PartialAssignment) (env : String → Option ℝ) :
    PartialEquations (l ++ r) env ↔ PartialEquations l env ∧ PartialEquations r env := by
  simp only [PartialEquations, List.forall_mem_append]

/-- A lowered body with atomics: its equations correspond to the source's in
every environment and for every atom reading. No premise is needed, because
integrals are rejected and the velocity equations are part of both sides. -/
structure AtomicLowered (sb : SourceBody) (c : Context) where
  assignments : List PartialAssignment
  outputs : assignments.map (·.output) = sb.outputs
  equations : ∀ atoms env, sb.Equations c atoms env ↔ PartialEquations assignments env
  velocityStates : sb.VelocityStates

/-- The diagnostic of a term that `Term.betaPartial` does not normalize: a
derivative under an atomic or in a denominator, or any other atom left. -/
private def derivativeCode (c : Context) (t : Term) : ErrorCode :=
  match t.checkDerivatives c with
  | .error .atomicDerivative => .atomicDerivative
  | _ => .unsupportedDerivative

/-- Lower an explicit assignment: collapse declared chains, read top-level atoms
as declared velocities, then beta-normalize keeping atomics. An atom that is not
read, including every atom under an atomic, is rejected. -/
private def lowerPartialAssignment (c : Context) (a : SourceAssignment) :
    Except Diagnostic {out : PartialAssignment // out.output = a.output ∧ ∀ atoms env,
      c.VelocitiesHold env →
      ((env a.output.name ≠ none ∧ a.rhs.eval env (c.rates env) atoms = env a.output.name) ↔
        (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name))} :=
  if a.rhs.integrals ≠ 0 then
    .error ⟨.unsupportedIntegral, a.output.id, "integral in an atomic declaration"⟩
  else match h : ((a.rhs.collapse c).readVelocities c a.output.name).betaPartial with
  | none => .error ⟨derivativeCode c ((a.rhs.collapse c).readVelocities c a.output.name),
      a.output.id, "derivative in an explicit assignment"⟩
  | some e => .ok ⟨⟨a.output, e⟩, rfl, fun atoms env hold => by
      rw [Term.betaPartial_correct _ e h env (c.rates env) atoms,
        Term.readVelocities_eval c _ _ env atoms hold, Term.collapse_eval]⟩

/-- Lower a differential equation: collapse declared chains, read lower-order
atoms as declared velocities, then isolate with partial residuals. -/
private def lowerPartialDifferential (c : Context) (d : DifferentialEquation) :
    Except Diagnostic {out : PartialAssignment // out.output = d.output ∧ ∀ atoms env,
      c.VelocitiesHold env →
      ((env d.output.name ≠ none ∧ ∃ v, d.lhs.eval env (c.rates env) atoms = some v ∧
          d.rhs.eval env (c.rates env) atoms = some v) ↔
        (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name))} :=
  if d.lhs.mentions d.output.name || d.rhs.mentions d.output.name then
    .error ⟨.repeatedDerivative, d.output.id, "derivative port named in its own equation"⟩
  else if d.lhs.integrals + d.rhs.integrals ≠ 0 then
    .error ⟨.unsupportedIntegral, d.output.id, "integral in an atomic declaration"⟩
  else match isolatePartial c d.output.name ((d.lhs.collapse c).readVelocities c d.output.name)
      ((d.rhs.collapse c).readVelocities c d.output.name) with
  | .error code => .error ⟨code, d.output.id, d.output.name⟩
  | .ok i => .ok ⟨⟨d.output, i.expr⟩, rfl, fun atoms env hold => by
      rw [← i.correct env atoms, Term.readVelocities_eval c _ _ env atoms hold,
        Term.readVelocities_eval c _ _ env atoms hold, Term.collapse_eval, Term.collapse_eval]⟩

/-- Lower a velocity declaration as the first-order equation it states, with no
premise, as in `Model.Source`. -/
private def lowerPartialVelocity (c : Context) (v : VelocityDeclaration) :
    Except Diagnostic {out : PartialAssignment // out.output = v.output ∧
      ∀ (atoms : Term → Option ℝ) env, True →
      ((env v.equation.output.name ≠ none ∧
          ∃ w, v.equation.lhs.eval env (c.rates env) atoms = some w ∧
            v.equation.rhs.eval env (c.rates env) atoms = some w) ↔
        (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name))} :=
  let d := v.equation
  if d.lhs.mentions d.output.name || d.rhs.mentions d.output.name then
    .error ⟨.repeatedDerivative, d.output.id, "derivative port named in its own equation"⟩
  else match isolatePartial c d.output.name d.lhs d.rhs with
  | .error code => .error ⟨code, d.output.id, d.output.name⟩
  | .ok i => .ok ⟨⟨d.output, i.expr⟩, rfl, fun atoms env _ => i.correct env atoms⟩

private def lowerPartialList {α : Type}
    (H : (Term → Option ℝ) → (String → Option ℝ) → Prop)
    (P : α → (Term → Option ℝ) → (String → Option ℝ) → Prop) (port : α → Port)
    (f : (a : α) → Except Diagnostic {out : PartialAssignment // out.output = port a ∧
      ∀ atoms env, H atoms env →
      (P a atoms env ↔ (env out.output.name ≠ none ∧ out.rhs.eval env = env out.output.name))}) :
    (as : List α) → Except Diagnostic {out : List PartialAssignment //
      out.map (·.output) = as.map port ∧ ∀ atoms env, H atoms env →
        ((∀ a ∈ as, P a atoms env) ↔ PartialEquations out env)}
  | [] => .ok ⟨[], rfl, fun _ _ _ => by simp [PartialEquations]⟩
  | a :: rest => do
      let ⟨x, hx, px⟩ ← f a
      let ⟨xs, hxs, pxs⟩ ← lowerPartialList H P port f rest
      return ⟨x :: xs, by simp [hx, hxs], fun atoms env hold => by
        have h1 := px atoms env hold
        have h2 := pxs atoms env hold
        simp only [List.forall_mem_cons, PartialEquations] at *
        rw [h1, h2]⟩

/-- Check scopes and velocity states, reject integral declarations, then lower
explicit assignments, differentials and velocity declarations, in source order. -/
def SourceBody.lowerAtomic (sb : SourceBody) (c : Context) (declares : sb.Declares c) :
    Except Diagnostic (AtomicLowered sb c) := do
  let names := (sb.inputs ++ sb.outputs).map Port.name
  for a in sb.assignments do
    match a.rhs.checkScope names with
    | .error name => throw ⟨.unknownReference, a.output.id, name⟩
    | .ok () => pure ()
  for d in sb.equations do
    match d.lhs.checkScope names, d.rhs.checkScope names with
    | .error name, _ | _, .error name => throw ⟨.unknownReference, d.output.id, name⟩
    | .ok (), .ok () => pure ()
  match hi : sb.integrals with
  | d :: _ =>
      throw ⟨.unsupportedIntegral, d.output.id, "integral declaration in an atomic declaration"⟩
  | [] =>
    if states : sb.VelocityStates then
      let ⟨as, has, pas⟩ ← lowerPartialList (fun _ env => c.VelocitiesHold env)
        _ (·.output) (lowerPartialAssignment c) sb.assignments
      let ⟨ds, hds, pds⟩ ← lowerPartialList (fun _ env => c.VelocitiesHold env)
        _ (·.output) (lowerPartialDifferential c) sb.differentials
      let ⟨vs, hvs, pvs⟩ ← lowerPartialList (fun _ _ => True) _ (·.output)
        (lowerPartialVelocity c) sb.velocities
      return ⟨as ++ ds ++ vs, by
        simp [SourceBody.outputs, SourceBody.equations, has, hds, hvs, hi, Function.comp_def,
          VelocityDeclaration.equation], fun atoms env => by
        simp only [SourceBody.Equations, SourceBody.equations, hi, List.map_nil,
          List.append_nil, List.forall_mem_append, List.forall_mem_map, partialEquations_append]
        rw [← pvs atoms env trivial]
        constructor
        · rintro ⟨ha, hd, hv⟩
          have hold := SourceBody.velocitiesHold declares hv
          exact ⟨⟨(pas atoms env hold).mp ha, (pds atoms env hold).mp hd⟩, hv⟩
        · rintro ⟨⟨ha, hd⟩, hv⟩
          have hold := SourceBody.velocitiesHold declares hv
          exact ⟨(pas atoms env hold).mpr ha, (pds atoms env hold).mpr hd, hv⟩, states⟩
    else
      match sb.velocities.find? (fun v =>
          !(sb.inputs.find? (·.name == v.velocity)).any (·.role == .state)) with
      | some v => throw ⟨.unsupportedRole, v.output.id, v.velocity⟩
      -- Unreachable: `VelocityStates` fails only through a declaration `find?` returns.
      | none => throw ⟨.unsupportedRole, "velocities", "declared velocity state"⟩

/-! ## Resolution to coordinate expressions

`Model.Resolution` for partial expressions. A resolved name holds a coordinate
`RealAtomics.Expr`, and it reads (`PartialEvaluated`) the expression's value only
where the expression is `Defined`. Every original equation is retained, so a
source environment agrees with the resolved values exactly (`PartialTrace.exact`),
and forces every resolved assignment to be `Defined`. -/

open RealAtomics (Expr)

def PartialExpr.resolve {k n : Nat} (env : String → Option (Expr k n)) :
    PartialExpr → Option (Expr k n)
  | .var name => env name
  | .constant q => some (.constant q)
  | .unary op a => (a.resolve env).map (.unary op)
  | .binary op a b => do return .binary op (← a.resolve env) (← b.resolve env)

/-- Each resolved name reads the value of its expression, where it is `Defined`. -/
noncomputable def PartialEvaluated {k n : Nat} (env : String → Option (Expr k n))
    (axes : Point k) (x : Point n) : String → Option ℝ :=
  fun name => (env name).bind (·.partialValue axes x)

theorem PartialExpr.resolve_correct {k n : Nat} (e : PartialExpr)
    (env : String → Option (Expr k n)) (axes : Point k) (x : Point n) :
    (e.resolve env).bind (·.partialValue axes x) = e.eval (PartialEvaluated env axes x) := by
  induction e with
  | var name => rfl
  | constant q => rfl
  | unary op a ha =>
      rw [PartialExpr.eval, ← ha]
      cases h : a.resolve env <;> simp [resolve, h, Expr.partialValue]
  | binary op a b ha hb =>
      rw [PartialExpr.eval, ← ha, ← hb]
      cases h : a.resolve env <;> cases h' : b.resolve env <;>
        simp [resolve, h, h', Expr.partialValue]

/-- A resolved expression reads the same through any environment that agrees with
the resolved values at every resolved name. -/
theorem PartialExpr.eval_resolved {k n : Nat} {e : PartialExpr}
    {env : String → Option (Expr k n)} {v : Expr k n} (h : e.resolve env = some v)
    {axes : Point k} {x : Point n} {source : String → Option ℝ}
    (agree : ∀ name w, env name = some w → w.partialValue axes x = source name) :
    e.eval (PartialEvaluated env axes x) = e.eval source := by
  induction e generalizing v with
  | var name => simp only [PartialExpr.eval, PartialEvaluated, resolve] at h ⊢; simp [h, agree _ _ h]
  | constant q => rfl
  | unary op a ha =>
      cases hA : a.resolve env with
      | none => simp [resolve, hA] at h
      | some w => simp only [PartialExpr.eval, ha hA]
  | binary op a b ha hb =>
      cases hA : a.resolve env with
      | none => simp [resolve, hA] at h
      | some w =>
        cases hB : b.resolve env with
        | none => simp [resolve, hA, hB] at h
        | some u => simp only [PartialExpr.eval, ha hA, hb hB]

/-- `Trace`, for partial assignments. -/
inductive PartialTrace {k n : Nat} (as : List PartialAssignment)
    (seed : String → Option (Expr k n)) : (String → Option (Expr k n)) → Type where
  | start : PartialTrace as seed seed
  | step {env} (previous : PartialTrace as seed env) (a : PartialAssignment)
      (member : a ∈ as) (value : Expr k n)
      (fresh : env a.output.name = none) (resolved : a.rhs.resolve env = some value) :
      PartialTrace as seed (Polynomial.bind env a.output.name value)

theorem PartialTrace.extends {k n : Nat} {as : List PartialAssignment}
    {seed env : String → Option (Expr k n)} (trace : PartialTrace as seed env) :
    Agrees seed env := by
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

/-- Wherever the seeds read as `source` does and `source` satisfies every
equation, every resolved name reads as `source` does: defined values agree, and a
resolved expression is `Defined` exactly where `source` has a value. -/
theorem PartialTrace.exact {k n : Nat} {as : List PartialAssignment}
    {seed env : String → Option (Expr k n)} (trace : PartialTrace as seed env)
    (axes : Point k) (x : Point n) (source : String → Option ℝ)
    (initial : ∀ name w, seed name = some w → w.partialValue axes x = source name)
    (equations : PartialEquations as source) :
    ∀ name w, env name = some w → w.partialValue axes x = source name := by
  induction trace with
  | start => exact initial
  | @step prev previous a member value fresh resolved ih =>
      intro name w h
      by_cases same : name = a.output.name
      · subst name
        simp only [Polynomial.bind, if_true, Option.some.injEq] at h
        subst h
        have hv := a.rhs.resolve_correct prev axes x
        rw [resolved, Option.bind_some, PartialExpr.eval_resolved resolved ih] at hv
        rw [hv, (equations a member).2]
      · exact ih name w (by simpa [Polynomial.bind, same] using h)

structure PartialReady {k n : Nat} (as : List PartialAssignment)
    (env : String → Option (Expr k n)) where
  assignment : PartialAssignment
  member : assignment ∈ as
  value : Expr k n
  fresh : env assignment.output.name = none
  resolved : assignment.rhs.resolve env = some value

/-- Stable tie-breaking: the first unresolved ready assignment in source order. -/
def partialNextReady {k n : Nat} (as : List PartialAssignment)
    (env : String → Option (Expr k n)) : Option (PartialReady as env) :=
  as.attach.findSome? fun a =>
    if fresh : env a.val.output.name = none then
      match resolved : a.val.rhs.resolve env with
      | none => none
      | some value => some ⟨a.val, a.property, value, fresh, resolved⟩
    else none

structure PartialResolution {k n : Nat} (as : List PartialAssignment)
    (seed : String → Option (Expr k n)) where
  env : String → Option (Expr k n)
  trace : PartialTrace as seed env

def partialSchedule {k n : Nat} {as : List PartialAssignment}
    {seed : String → Option (Expr k n)} :
    Nat → PartialResolution as seed → PartialResolution as seed
  | 0, result => result
  | fuel + 1, result =>
      match partialNextReady as result.env with
      | none => result
      | some ready => partialSchedule fuel
          ⟨Polynomial.bind result.env ready.assignment.output.name ready.value,
            .step result.trace ready.assignment ready.member ready.value ready.fresh
              ready.resolved⟩

def PartialComplete {k n : Nat} (as : List PartialAssignment)
    (env : String → Option (Expr k n)) : Prop :=
  ∀ a ∈ as, env a.output.name ≠ none ∧ a.rhs.resolve env = env a.output.name

instance {k n : Nat} (as : List PartialAssignment) (env : String → Option (Expr k n)) :
    Decidable (PartialComplete as env) := by unfold PartialComplete; infer_instance

/-- A complete resolution satisfies every equation at a point where every resolved
assignment is `Defined`. -/
theorem partial_equations {k n : Nat} {as : List PartialAssignment}
    {env : String → Option (Expr k n)} (complete : PartialComplete as env)
    (axes : Point k) (x : Point n)
    (defined : ∀ a ∈ as, ∃ w, env a.output.name = some w ∧ w.Defined axes x) :
    PartialEquations as (PartialEvaluated env axes x) := by
  intro a member
  obtain ⟨w, hw, hd⟩ := defined a member
  have hv : w.partialValue axes x = some (w.value axes x) :=
    (w.partialValue_eq_some axes x _).mpr ⟨hd, rfl⟩
  refine ⟨by simp [PartialEvaluated, hw, hv], ?_⟩
  rw [← a.rhs.resolve_correct, (complete a member).2]
  rfl

/-! ## Seeds -/

/-- Runtime inputs as coordinates and bound parameters as exact constants, as
`Body.seed` does. -/
def SourceBody.partialSeed {k n : Nat} (sb : SourceBody) (ids : Fin n → String)
    (name : String) : Option (Expr k n) :=
  (sb.inputs.find? (·.name == name)).bind fun p =>
    if p.role == .parameter then ((sb.withAssignments []).parameter p.id).map .constant
    else (index ids p.id).map .input

theorem SourceBody.partialSeed_value {k n : Nat} (sb : SourceBody) (ids : Fin n → String)
    (axes : Point k) (x : Point n) {name : String} {w : Expr k n}
    (h : sb.partialSeed ids name = some w) :
    ∃ v, w.partialValue axes x = some v ∧ sb.inputEnvironment ids x name = some v := by
  simp only [SourceBody.partialSeed, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, hw⟩ := h
  simp only [SourceBody.inputEnvironment, Body.inputEnvironment, SourceBody.withAssignments, hp,
    Option.bind_some, Body.inputValue]
  split at hw
  · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hw
    simp_all [Expr.partialValue, SourceBody.withAssignments]
  · obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hw
    simp_all [Expr.partialValue]

theorem SourceBody.partialSeed_input {k n : Nat} (sb : SourceBody) (ids : Fin n → String)
    (axes : Point k) (x : Point n) {name : String} {v : ℝ}
    (h : sb.inputEnvironment ids x name = some v) :
    ∃ w, sb.partialSeed (k := k) ids name = some w ∧ w.partialValue axes x = some v := by
  simp only [SourceBody.inputEnvironment, Body.inputEnvironment, SourceBody.withAssignments,
    Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, hv⟩ := h
  simp only [SourceBody.partialSeed, hp, Option.bind_some]
  simp only [Body.inputValue] at hv
  split at hv
  · obtain ⟨q, hq, rfl⟩ := Option.map_eq_some_iff.mp hv
    refine ⟨.constant q, ?_, rfl⟩
    simp_all [SourceBody.withAssignments]
  · obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp hv
    refine ⟨.input i, ?_, rfl⟩
    simp_all

theorem SourceBody.value_partialEvaluated {k n : Nat} (sb : SourceBody)
    (env : String → Option (Expr k n)) (axes : Point k) (x : Point n) (id : String) :
    sb.value (PartialEvaluated env axes x) id = (sb.value env id).bind (·.partialValue axes x) := by
  unfold SourceBody.value
  cases (sb.inputs ++ sb.outputs).find? (·.id == id) <;> rfl

/-! ## Resolved bodies -/

/-- Every lowered assignment resolved, from the seeds of `ids`, with each
assignment's coordinate expression: `guards` holds one per assignment, in source
order. -/
structure AtomicResolved (k n : Nat) (sb : SourceBody) (as : List PartialAssignment)
    (ids : Fin n → String) where
  env : String → Option (Expr k n)
  trace : PartialTrace as (sb.partialSeed ids) env
  complete : PartialComplete as env
  guards : Fin as.length → Expr k n
  guardsFound : ∀ j : Fin as.length, env as[j].output.name = some (guards j)

def resolveAtomic {k n : Nat} (sb : SourceBody) (as : List PartialAssignment)
    (ids : Fin n → String) : Except Diagnostic (AtomicResolved k n sb as ids) :=
  if ∀ p ∈ sb.inputs, (sb.partialSeed (k := k) ids p.name).isSome then
    let result := partialSchedule as.length ⟨sb.partialSeed ids, .start⟩
    if hc : PartialComplete as result.env then
      match hg : Dynamics.resolveTable (fun j : Fin as.length => result.env as[j].output.name) with
      | some guards =>
          .ok ⟨result.env, result.trace, hc, guards, Dynamics.resolveTable_correct _ _ hg⟩
      -- Unreachable: a complete resolution names every output.
      | none => .error ⟨.incompleteResolution, "equations", "final symbolic environment"⟩
    else
      match as.find? (fun a => (result.env a.output.name).isNone) with
      | some a => .error ⟨.cyclicDependency, a.output.id, a.output.name⟩
      | none => .error ⟨.incompleteResolution, "equations", "final symbolic environment"⟩
  else .error ⟨.missingBinding, "inputs", "runtime coordinate or fixed parameter"⟩

/-- The source equations with atomics, at one point, against the resolved
expressions: an environment satisfying them and reading `refs` with property `P`
exists exactly where every resolved assignment and every selected expression is
`Defined` and the selected values have `P`. Unused assignments keep their domains. -/
theorem AtomicResolved.source_iff {sb : SourceBody} {c : Context} (l : AtomicLowered sb c)
    {k n m : Nat} {ids : Fin n → String} (p : AtomicResolved k n sb l.assignments ids)
    (refs : Fin m → String) (outs : Fin m → Expr k n)
    (found : ∀ i, sb.value p.env (refs i) = some (outs i)) (atoms : Term → Option ℝ)
    (axes : Point k) (x : Point n) (P : Fin m → ℝ → Prop) :
    (∃ env, sb.Source c atoms ids x env ∧ ∀ i, ∃ r, sb.value env (refs i) = some r ∧ P i r) ↔
      ((∀ i, (outs i).Defined axes x) ∧ ∀ j, (p.guards j).Defined axes x) ∧
        ∀ i, P i ((outs i).value axes x) := by
  constructor
  · rintro ⟨env, ⟨agrees, equations⟩, hrefs⟩
    have peqs := (l.equations atoms env).mp equations
    have exact := p.trace.exact axes x env (fun name w hw => by
      obtain ⟨v, hv, hi⟩ := sb.partialSeed_value ids axes x hw
      rw [hv, agrees name v hi]) peqs
    have value_exact : ∀ id w, sb.value p.env id = some w →
        sb.value env id = w.partialValue axes x := by
      intro id w hw
      rw [SourceBody.value_eq] at hw ⊢
      cases hn : sb.portName id with
      | none => simp [hn] at hw
      | some name =>
          simp only [hn, Option.bind_some] at hw ⊢
          exact (exact name w hw).symm
    refine ⟨⟨fun i => ?_, fun j => ?_⟩, fun i => ?_⟩
    · obtain ⟨r, hr, -⟩ := hrefs i
      rw [value_exact _ _ (found i)] at hr
      exact ((outs i).partialValue_eq_some axes x r |>.mp hr).1
    · have member : l.assignments[j] ∈ l.assignments := List.getElem_mem _
      have hv := exact _ _ (p.guardsFound j)
      obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.mp (peqs _ member).1
      rw [hr] at hv
      exact ((p.guards j).partialValue_eq_some axes x r |>.mp hv).1
    · obtain ⟨r, hr, hp⟩ := hrefs i
      rw [value_exact _ _ (found i)] at hr
      obtain ⟨-, rfl⟩ := (outs i).partialValue_eq_some axes x r |>.mp hr
      exact hp
  · rintro ⟨⟨houts, hguards⟩, hp⟩
    refine ⟨PartialEvaluated p.env axes x, ⟨fun name v hv => ?_, ?_⟩, fun i => ?_⟩
    · obtain ⟨w, hw, hwv⟩ := sb.partialSeed_input (k := k) ids axes x hv
      simp [PartialEvaluated, p.trace.extends name w hw, hwv]
    · refine (l.equations atoms _).mpr (partial_equations p.complete axes x fun a member => ?_)
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem member
      exact ⟨_, p.guardsFound ⟨j, hj⟩, hguards ⟨j, hj⟩⟩
    · refine ⟨(outs i).value axes x, ?_, hp i⟩
      rw [SourceBody.value_partialEvaluated, found i, Option.bind_some]
      exact ((outs i).partialValue_eq_some axes x _).mpr ⟨houts i, rfl⟩

/-! ## Compilation -/

/-- The runtime coordinates of a polynomial declaration, as `Body.runtimeIds`. -/
def SourceBody.runtimeIds (sb : SourceBody) :
    Fin (sb.withAssignments []).runtimePorts.length → String :=
  (sb.withAssignments []).runtimeIds

/-- A compiled polynomial declaration with atomics: every lowered assignment
resolved over the runtime coordinates, and each observation's expression. -/
structure AtomicPolynomialModel (sb : SourceBody) where
  valid : (Declaration.polynomial sb.interface).validate = .ok ()
  lowered : AtomicLowered sb Context.empty
  resolved : AtomicResolved 0 (sb.withAssignments []).runtimePorts.length sb
    lowered.assignments sb.runtimeIds
  outputs : Fin sb.observations.length → Expr 0 (sb.withAssignments []).runtimePorts.length
  found : ∀ i, sb.value resolved.env (sb.observationIds i) = some (outputs i)

/-- The observations, guarded by every resolved assignment. -/
def AtomicPolynomialModel.circuit {sb : SourceBody} (p : AtomicPolynomialModel sb) :
    RealAtomics.Circuit 0 (sb.withAssignments []).runtimePorts.length sb.observations.length :=
  RealAtomics.guardedField p.outputs p.resolved.guards

/-- As `compileSourcePolynomial`, with atomics: no evolution axis, so every
derivative atom, differential equation, velocity and integral declaration and
every integral is rejected. -/
def compileAtomicPolynomial (sb : SourceBody) : Except Diagnostic (AtomicPolynomialModel sb) := do
  if let some d := sb.integrals.head? then
    throw ⟨.unsupportedIntegral, d.output.id, "integral without an evolution axis"⟩
  if let some d := sb.equations.head? then
    throw ⟨.unsupportedDerivative, d.output.id, "differential equation without an evolution axis"⟩
  if let some a := sb.assignments.find? (·.rhs.integrals ≠ 0) then
    throw ⟨.unsupportedIntegral, a.output.id, "integral without an evolution axis"⟩
  match hv : (Declaration.polynomial sb.interface).validate with
  | .error error => throw error
  | .ok () =>
    let lowered ← sb.lowerAtomic Context.empty sb.declares_empty
    let resolved ← resolveAtomic sb lowered.assignments sb.runtimeIds
    match hs : Dynamics.resolveTable (fun i => sb.value resolved.env (sb.observationIds i)) with
    | none => throw ⟨.unknownReference, "observations", "selected source ID"⟩
    | some outputs =>
        return ⟨hv, lowered, resolved, outputs, Dynamics.resolveTable_correct _ _ hs⟩

/-- The original source equations, atomics and lambdas included, against the
compiled circuit's operational relation. Both sides require every assignment,
used or not, to be inside its domain. -/
theorem AtomicPolynomialModel.correct {sb : SourceBody} (p : AtomicPolynomialModel sb)
    (axes : Point 0) (x : Point (sb.withAssignments []).runtimePorts.length)
    (y : Point sb.observations.length) :
    sb.Observes Context.empty sb.runtimeIds sb.observationIds x y ↔ p.circuit.Rel axes x y := by
  rw [AtomicPolynomialModel.circuit, RealAtomics.guardedField_rel]
  have key := p.resolved.source_iff p.lowered sb.observationIds p.outputs p.found (fun _ => none)
    axes x (fun i r => r = y i)
  simp only [exists_eq_right] at key
  rw [SourceBody.Observes, key]
  constructor
  · rintro ⟨hd, hy⟩
    exact ⟨hd, funext fun i => (hy i).symm⟩
  · rintro ⟨hd, rfl⟩
    exact ⟨hd, fun _ => rfl⟩

/-- A compiled continuous declaration with atomics: every lowered assignment
resolved over the state coordinates, each state's rate, and the initial values. -/
structure AtomicContinuousModel (sb : SourceBody) (e : Evolution) where
  valid : (Declaration.continuous sb.interface e).validate = .ok ()
  lowered : AtomicLowered sb (sb.context e)
  resolved : AtomicResolved 1 e.states.length sb lowered.assignments e.stateIds
  rates : Fin e.states.length → Expr 1 e.states.length
  ratesFound : ∀ i, sb.value resolved.env (e.derivativeIds i) = some (rates i)
  initials : Fin e.states.length → ℚ
  initialFound : ∀ i, e.initialValue e.states[i].initialId = some (initials i)

noncomputable def AtomicContinuousModel.initial {sb : SourceBody} {e : Evolution}
    (p : AtomicContinuousModel sb e) : Point e.states.length := fun i => p.initials i

/-- The partial vector field: the rates, guarded by every resolved assignment,
adapted to the no-driver interface as `ContinuousModel.field` is. -/
def AtomicContinuousModel.field {sb : SourceBody} {e : Evolution}
    (p : AtomicContinuousModel sb e) :
    RealAtomics.Circuit 1 (0 + e.states.length) e.states.length :=
  .compose (.embed (Polynomial.route (fun i => Fin.natAdd 0 i)))
    (RealAtomics.guardedField p.rates p.resolved.guards)

/-- The partial-field feedback of `RealAtomics.Feedback`, from the declared
initial values. Its relation requires the field to be `Defined` along the state
at every time of the forward domain. -/
def AtomicContinuousModel.Closes {sb : SourceBody} {e : Evolution}
    (p : AtomicContinuousModel sb e) (state : Dynamics.Signal e.states.length) : Prop :=
  p.field.CloseRel e.axis.id e.time (Dynamics.signalAppend noDrivers (fun _ => p.initial)) state

/-- As `compileSourceContinuous`, with atomics. -/
def compileAtomicContinuous (sb : SourceBody) (e : Evolution) :
    Except Diagnostic (AtomicContinuousModel sb e) :=
  match hv : (Declaration.continuous sb.interface e).validate with
  | .error error => .error error
  | .ok () => do
    let lowered ← sb.lowerAtomic (sb.context e) (sb.declares_context e)
    let resolved ← resolveAtomic sb lowered.assignments e.stateIds
    match hr : Dynamics.resolveTable (fun i => sb.value resolved.env (e.derivativeIds i)) with
    | none => .error ⟨.unknownReference, "outputs", "derivative ID"⟩
    | some rates =>
      match hi : Dynamics.resolveTable (fun i => e.initialValue e.states[i].initialId) with
      | none => .error ⟨.missingBinding, "initialValues", "state initial ID"⟩
      | some initials => return ⟨hv, lowered, resolved, rates,
          Dynamics.resolveTable_correct _ _ hr, initials, Dynamics.resolveTable_correct _ _ hi⟩

/-- The original source with atomics and its initial conditions, against the
initialized ODE of the compiled rates, with every resolved assignment `Defined`
along the state at every time of the forward domain. -/
theorem AtomicContinuousModel.solves_iff {sb : SourceBody} {e : Evolution}
    (p : AtomicContinuousModel sb e) (state : Dynamics.Signal e.states.length) :
    sb.Solves e state ↔ state e.time.start = p.initial ∧ ∀ t ∈ e.time.domain,
      ((∀ i, (p.rates i).Defined (RealAtomics.timeAxis t) (state t)) ∧
        ∀ j, (p.resolved.guards j).Defined (RealAtomics.timeAxis t) (state t)) ∧
      ∀ i, HasDerivWithinAt (fun t => state t i)
        ((p.rates i).value (RealAtomics.timeAxis t) (state t)) e.time.domain t := by
  unfold SourceBody.Solves
  have initials : (∀ i, (e.initialValue e.states[i].initialId).map (fun q : ℚ => (q : ℝ)) =
      some (state e.time.start i)) ↔ state e.time.start = p.initial := by
    simp only [p.initialFound, Option.map_some, Option.some.injEq]
    exact ⟨fun h => funext (fun i => (h i).symm), fun h i => (congrFun h i).symm⟩
  rw [initials]
  refine and_congr_right fun _ => forall₂_congr fun t _ => ?_
  exact p.resolved.source_iff p.lowered e.derivativeIds p.rates p.ratesFound _
    (RealAtomics.timeAxis t) (state t)
    (fun i r => HasDerivWithinAt (fun t => state t i) r e.time.domain t)

@[simp] private theorem route_natAdd {n : Nat} (u : Point 0) (x : Point n) :
    (Polynomial.route (fun i : Fin n => Fin.natAdd 0 i)).run (pointAppend u x) = x := by
  funext i
  simp [pointAppend]

/-- The same correspondence through the partial-field feedback relation: the
original source with atomics has exactly the realizations of the compiled
partial field as solutions, same states, start, forward domain and initial data.
It asserts no existence or uniqueness. -/
theorem AtomicContinuousModel.solves_iff_closes {sb : SourceBody} {e : Evolution}
    (p : AtomicContinuousModel sb e) (state : Dynamics.Signal e.states.length) :
    sb.Solves e state ↔ p.Closes state := by
  rw [p.solves_iff, AtomicContinuousModel.Closes, RealAtomics.Circuit.close_correct]
  simp only [AtomicContinuousModel.field, RealAtomics.Circuit.Defined, RealAtomics.Circuit.value,
    route_natAdd, RealAtomics.guardedField_defined, RealAtomics.guardedField_value, true_and,
    Evolution.time]

#print axioms RealAtomics.Expr.partialValue_eq_some
#print axioms RealAtomics.guardedField_rel
#print axioms Term.betaPartial_correct
#print axioms Term.partialAffine_correct
#print axioms PartialIsolated.correct
#print axioms PartialTrace.exact
#print axioms AtomicResolved.source_iff
#print axioms AtomicPolynomialModel.correct
#print axioms AtomicContinuousModel.solves_iff
#print axioms AtomicContinuousModel.solves_iff_closes
end Gimle.Asgard.Model
