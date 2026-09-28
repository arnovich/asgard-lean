import Gimle.Asgard.Model.Differential
import Gimle.Asgard.Model.Resolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Source integrals over the evolution axis, from the declared start, and the
three inverse rewrites between integrals and derivatives, and the reading of
declared integral states.

## Semantics

An integral `I_t(X)` depends on the whole trajectory, so `Term.eval` reads it
through an `atoms` oracle. `Term.along` is the trajectory reading that fills it:
a term is read at every time `s` of the forward half-line `s ≥ start`, names
from the inputs at `s`, derivative chains through a supplied chain reading, and

- `I_t(X)` at `t` is `F t`, where `F` is the antiderivative of the reading of
  `X` on the half-line that vanishes at `start` (`primitiveFrom`);
- `D_t(Y)` of an operand `Y` that is not a chain is the derivative within the
  half-line of the reading of `Y` (`derivFrom`).

Neither is totalized. Both depend on the reading over the whole half-line,
after `t` as well. If the reading of `X` is undefined somewhere on the
half-line, or is not a derivative there, `I_t(X)` has no value; it is never a
Lebesgue or Riemann integral that silently returns `0` for a non-integrable
integrand. The antiderivative is unique (`primitiveFrom_eq`), and for a
continuous integrand it is the interval integral (`primitiveFrom_eq_integral`).
An integrand without an antiderivative has no integral here even when it is
Lebesgue-integrable. Every integrand the rewrites below accept has an
antiderivative along a regular trajectory (`Term.tame_primitive`); for a
continuous one it is the interval integral.

## Inverse rewrites

`Term.cancelAtom` recognizes exactly three inverse shapes, all on the evolution
axis, and reads declared integral states (below):

- `D_t(I_t(X))` becomes `X`, when `X` is `Term.tame`: a polynomial in inputs
  plus literal multiples of first-order state derivatives. The derivative of the
  integral is the integrand (`Term.along_derivative_integral`).
- `D_t(D_t(I_t(x)))` becomes `D_t(x)`, for a state `x` with a declared initial
  value; the proof reads the continuity of `x` from that declaration.
- `I_t(D_t(x))` becomes `x - x0`, for a state `x` whose declared initial value is
  `x0`. The boundary term is kept: `I_t(D_t(x))` is `x - x(start)`
  (`Term.along_integral_derivative`), and `x` alone is wrong whenever
  `x(start) ≠ 0` (`integral_derivative_ne`).

## Declared integral states

An integral no inverse rewrite removes is read as a declared state: when the
boundary declares `F` as the integral of `X` (`Boundary.integral`), `I_t(X)`
becomes `F`. Nothing is inferred. The trajectory must make `F` the
antiderivative of the reading of `X` that vanishes at the start
(`Trajectory.Regular.integral`); then `I_t(X)` reads `F` at every time, because
the antiderivative from the start is unique (`primitiveFrom_iff`).

`Term.cancel` applies all four at the atom positions of a sum, product or
negation. Every other integral is left in place and rejected by lowering. The
rewrite is exact wherever the atoms are read along the trajectory
(`Context.Cancels`), and `Context.cancels` discharges that premise for every
trajectory whose states are differentiable, whose ports carry the actual
derivatives, whose declared initial values hold and whose declared integral
states are antiderivatives of their integrands: in particular, at every time of a
solution of the source or of the lowered body. -/
namespace Gimle.Asgard.Model
open Polynomial Set

/-! ## Primitives and derivatives on the forward half-line -/

open Classical in
/-- The antiderivative of `f` on `Ici start` that vanishes at `start`, at `t`:
`f` must be defined on the whole half-line and be the derivative there. -/
noncomputable def primitiveFrom (start : ℝ) (f : ℝ → Option ℝ) (t : ℝ) : Option ℝ :=
  if h : ∃ F : ℝ → ℝ, F start = 0 ∧
      ∀ s ∈ Ici start, ∃ x, f s = some x ∧ HasDerivWithinAt F x (Ici start) s then
    some (h.choose t)
  else none

open Classical in
/-- The derivative within `Ici start` at `t` of `f`, which must be defined on the
whole half-line and differentiable at `t`. -/
noncomputable def derivFrom (start : ℝ) (f : ℝ → Option ℝ) (t : ℝ) : Option ℝ :=
  if h : ∃ g : ℝ → ℝ, (∀ s ∈ Ici start, f s = some (g s)) ∧
      DifferentiableWithinAt ℝ g (Ici start) t then
    some (derivWithin h.choose (Ici start) t)
  else none

/-- Two functions with the same derivative within the half-line, everywhere on it,
and the same value at its start, agree on it. -/
theorem eqOn_of_hasDerivWithinAt {start : ℝ} {F G f : ℝ → ℝ}
    (hF : ∀ s ∈ Ici start, HasDerivWithinAt F (f s) (Ici start) s)
    (hG : ∀ s ∈ Ici start, HasDerivWithinAt G (f s) (Ici start) s)
    (h0 : F start = G start) : EqOn F G (Ici start) := by
  intro t ht
  have hcont : ContinuousOn (fun s => F s - G s) (Icc start t) := fun s hs =>
    ((hF s hs.1).sub (hG s hs.1)).continuousWithinAt.mono Icc_subset_Ici_self
  have hzero : ∀ s ∈ Ico start t, HasDerivWithinAt (fun s => F s - G s) 0 (Ici s) s := by
    intro s hs
    have := (hF s hs.1).sub (hG s hs.1)
    rw [sub_self] at this
    exact this.mono (Ici_subset_Ici.mpr hs.1)
  have := constant_of_has_deriv_right_zero hcont hzero t ⟨ht, le_refl t⟩
  rw [h0, sub_self] at this
  exact sub_eq_zero.mp this

/-- `primitiveFrom` is the antiderivative that vanishes at `start`, whichever one
is chosen: it is unique on the half-line. -/
theorem primitiveFrom_eq {start : ℝ} {f : ℝ → Option ℝ} {F g : ℝ → ℝ} (h0 : F start = 0)
    (hf : ∀ s ∈ Ici start, f s = some (g s))
    (hF : ∀ s ∈ Ici start, HasDerivWithinAt F (g s) (Ici start) s) {t : ℝ} (ht : t ∈ Ici start) :
    primitiveFrom start f t = some (F t) := by
  have ex : ∃ F : ℝ → ℝ, F start = 0 ∧
      ∀ s ∈ Ici start, ∃ x, f s = some x ∧ HasDerivWithinAt F x (Ici start) s :=
    ⟨F, h0, fun s hs => ⟨g s, hf s hs, hF s hs⟩⟩
  rw [primitiveFrom, dif_pos ex]
  obtain ⟨c0, cd⟩ := ex.choose_spec
  have hc : ∀ s ∈ Ici start, HasDerivWithinAt ex.choose (g s) (Ici start) s := by
    intro s hs
    obtain ⟨x, hx, hd⟩ := cd s hs
    rw [hf s hs, Option.some.injEq] at hx
    exact hx ▸ hd
  rw [eqOn_of_hasDerivWithinAt hc hF (c0.trans h0.symm) ht]

/-- `derivFrom` is the derivative within the half-line of any function that
represents `f` there. -/
theorem derivFrom_eq {start : ℝ} {f : ℝ → Option ℝ} {g : ℝ → ℝ} {r t : ℝ}
    (hf : ∀ s ∈ Ici start, f s = some (g s)) (hd : HasDerivWithinAt g r (Ici start) t)
    (ht : t ∈ Ici start) : derivFrom start f t = some r := by
  have ex : ∃ g : ℝ → ℝ, (∀ s ∈ Ici start, f s = some (g s)) ∧
      DifferentiableWithinAt ℝ g (Ici start) t := ⟨g, hf, hd.differentiableWithinAt⟩
  rw [derivFrom, dif_pos ex]
  obtain ⟨cf, -⟩ := ex.choose_spec
  have eq : EqOn ex.choose g (Ici start) := by
    intro s hs
    have := (cf s hs).symm.trans (hf s hs)
    exact Option.some.inj this
  rw [derivWithin_congr eq (eq ht), hd.derivWithin (uniqueDiffOn_Ici start t ht)]

/-- Fundamental theorem of calculus on the half-line: a continuous function has
an antiderivative there, the interval integral from `start`. -/
theorem exists_primitive_of_continuousOn {start : ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici start)) :
    ∃ F : ℝ → ℝ, F start = 0 ∧ (∀ s ∈ Ici start, HasDerivWithinAt F (g s) (Ici start) s) ∧
      ∀ t ∈ Ici start, F t = ∫ s in start..t, g s := by
  have hext : Continuous (fun s => g (max start s)) :=
    hg.comp_continuous (continuous_const.max continuous_id)
      (fun s => show start ≤ max start s from le_max_left _ _)
  refine ⟨fun u => ∫ s in start..u, g (max start s), by simp, fun s hs => ?_, fun t ht => ?_⟩
  · have := (hext.integral_hasStrictDerivAt start s).hasDerivAt.hasDerivWithinAt (s := Ici start)
    rwa [max_eq_right hs] at this
  · refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    simp only [max_eq_right hs.1]

/-- For a continuous integrand, `primitiveFrom` is the interval integral from
`start`: nothing new is claimed where the Lebesgue integral applies. -/
theorem primitiveFrom_eq_integral {start : ℝ} {f : ℝ → Option ℝ} {g : ℝ → ℝ}
    (hg : ContinuousOn g (Ici start)) (hf : ∀ s ∈ Ici start, f s = some (g s)) {t : ℝ}
    (ht : t ∈ Ici start) : primitiveFrom start f t = some (∫ s in start..t, g s) := by
  obtain ⟨F, h0, hF, hi⟩ := exists_primitive_of_continuousOn hg
  rw [primitiveFrom_eq h0 hf hF ht, hi t ht]

/-- A function is the integral from `start` at every time of the half-line
exactly when it vanishes at `start` and is an antiderivative there. This is what
makes a declared integral state `F = I_t(X)` the pair `D_t(F) = X`, `F(start) = 0`. -/
theorem primitiveFrom_iff {start : ℝ} {f : ℝ → Option ℝ} {g : ℝ → ℝ} :
    (∀ t ∈ Ici start, primitiveFrom start f t = some (g t)) ↔
      g start = 0 ∧ ∀ s ∈ Ici start, ∃ x, f s = some x ∧ HasDerivWithinAt g x (Ici start) s := by
  constructor
  · intro h
    have h0 := h start self_mem_Ici
    unfold primitiveFrom at h0
    split_ifs at h0 with ex
    obtain ⟨c0, cd⟩ := ex.choose_spec
    have eq : ∀ t ∈ Ici start, ex.choose t = g t := by
      intro t ht
      have := h t ht
      rw [primitiveFrom, dif_pos ex, Option.some.injEq] at this
      exact this
    refine ⟨(Option.some.inj h0) ▸ c0, fun s hs => ?_⟩
    obtain ⟨x, hx, hd⟩ := cd s hs
    exact ⟨x, hx, hd.congr_of_mem (fun y hy => (eq y hy).symm) hs⟩
  · rintro ⟨h0, hd⟩ t ht
    have ex : ∃ F : ℝ → ℝ, F start = 0 ∧
        ∀ s ∈ Ici start, ∃ x, f s = some x ∧ HasDerivWithinAt F x (Ici start) s := ⟨g, h0, hd⟩
    rw [primitiveFrom, dif_pos ex]
    obtain ⟨c0, cd⟩ := ex.choose_spec
    have deriv : ∀ {G : ℝ → ℝ}, (∀ s ∈ Ici start, ∃ x, f s = some x ∧
        HasDerivWithinAt G x (Ici start) s) →
        ∀ s ∈ Ici start, HasDerivWithinAt G (derivWithin g (Ici start) s) (Ici start) s := by
      intro G hG s hs
      obtain ⟨x, hx, hGd⟩ := hG s hs
      obtain ⟨y, hy, hgd⟩ := hd s hs
      rw [hx, Option.some.injEq] at hy
      rw [hgd.derivWithin (uniqueDiffOn_Ici start s hs), ← hy]
      exact hGd
    rw [eqOn_of_hasDerivWithinAt (deriv cd) (deriv hd) (c0.trans h0.symm) ht]

/-! ## The trajectory reading -/

/-- A trajectory as the source reads it: at each time `s`, the names in `base s`
and the derivative chains in `rates s` (axes outermost first, as in
`Term.eval`), on the forward half-line of `axis` from `start`. -/
structure Trajectory where
  axis : String
  start : ℝ
  base : ℝ → String → Option ℝ
  rates : ℝ → List String → String → Option ℝ

/-- The reading of a term at every time of a trajectory. A lambda rebinds its
binder along the whole trajectory, and masks chains based on it, exactly as
`Term.eval` does at one time. -/
noncomputable def Term.along : Term → Trajectory → ℝ → Option ℝ
  | .var name, T, s => T.base s name
  | .constant q, _, _ => some q
  | .add a b, T, s => do return (← a.along T s) + (← b.along T s)
  | .mul a b, T, s => do return (← a.along T s) * (← b.along T s)
  | .neg a, T, s => do return -(← a.along T s)
  | .apply x body arg, T, s =>
      body.along { T with
        base := fun s' => rebind (T.base s') x (arg.along T s')
        rates := fun s' a n => if n = x then none else T.rates s' a n } s
  | .derivative axis operand, T, s =>
      match operand.chain with
      | some (axes, state) => T.rates s (axis :: axes) state
      | none => if axis = T.axis then derivFrom T.start (operand.along T) s else none
  | .integral axis operand, T, s =>
      if axis = T.axis then primitiveFrom T.start (operand.along T) s else none

/-- The non-local atoms of `Term.eval`, read along a trajectory at `t`. -/
noncomputable def Trajectory.atoms (T : Trajectory) (t : ℝ) : Term → Option ℝ :=
  fun u => u.along T t

/-- An integral denotes the antiderivative of its integrand from the start:
whenever `I_t(X)` has a value `w` at `t`, the reading of `X` is defined on the
whole half-line and is the derivative there of a function that vanishes at the
start and is `w` at `t`. -/
theorem Term.along_integral {T : Trajectory} {X : Term} {t w : ℝ}
    (h : (Term.integral T.axis X).along T t = some w) :
    ∃ F : ℝ → ℝ, F T.start = 0 ∧ F t = w ∧
      ∀ s ∈ Ici T.start, ∃ x, X.along T s = some x ∧ HasDerivWithinAt F x (Ici T.start) s := by
  simp only [Term.along, ite_true, primitiveFrom] at h
  split_ifs at h with ex
  obtain ⟨h0, hd⟩ := ex.choose_spec
  exact ⟨ex.choose, h0, Option.some.inj h, hd⟩

/-- The derivative of an integral is its integrand, wherever the integrand has
an antiderivative on the half-line: `D_t(I_t(X))` reduces to `X`. -/
theorem Term.along_derivative_integral {T : Trajectory} {X : Term} {F g : ℝ → ℝ}
    (h0 : F T.start = 0) (hX : ∀ s ∈ Ici T.start, X.along T s = some (g s))
    (hF : ∀ s ∈ Ici T.start, HasDerivWithinAt F (g s) (Ici T.start) s) {t : ℝ}
    (ht : t ∈ Ici T.start) :
    (Term.derivative T.axis (.integral T.axis X)).along T t = X.along T t := by
  have hI : ∀ s ∈ Ici T.start, primitiveFrom T.start (X.along T) s = some (F s) :=
    fun s hs => primitiveFrom_eq h0 hX hF hs
  simp only [Term.along, Term.chain, ite_true]
  exact (derivFrom_eq hI (hF t ht) ht).trans (hX t ht).symm

/-- The integral of a derivative keeps its boundary term: `I_t(D_t(x))` is
`x - x(start)`, never `x`. -/
theorem Term.along_integral_derivative {T : Trajectory} {x : String} {g : ℝ → ℝ}
    (hd : ∀ s ∈ Ici T.start, DifferentiableWithinAt ℝ g (Ici T.start) s ∧
      T.rates s [T.axis] x = some (derivWithin g (Ici T.start) s)) {t : ℝ}
    (ht : t ∈ Ici T.start) :
    (Term.integral T.axis (.derivative T.axis (.var x))).along T t = some (g t - g T.start) := by
  simp only [Term.along, Term.chain, ite_true]
  refine primitiveFrom_eq (F := fun s => g s - g T.start) (g := fun s => derivWithin g _ s)
    (sub_self _) (fun s hs => (hd s hs).2) (fun s hs => ?_) ht
  exact ((hd s hs).1.hasDerivWithinAt).sub_const _

/-- Dropping the boundary term is wrong: on the constant trajectory `x = 1`,
`I_t(D_t(x))` is `0` while `x` is `1`. -/
theorem integral_derivative_ne : ∃ (T : Trajectory) (t : ℝ),
    (Term.integral T.axis (.derivative T.axis (.var "x"))).along T t ≠
      (Term.var "x").along T t := by
  refine ⟨⟨"t", 0, fun _ _ => some 1, fun _ _ _ => some 0⟩, 0, ?_⟩
  have := Term.along_integral_derivative (T := ⟨"t", 0, fun _ _ => some 1, fun _ _ _ => some 0⟩)
    (x := "x") (g := fun _ => 1) (fun s _ => ⟨differentiableWithinAt_const _, by simp⟩)
    (t := 0) self_mem_Ici
  rw [this]
  simp [Term.along]

/-! ## The rewrites -/

/-- A polynomial in names that `bd.input` reads from states or bound parameters,
so its reading is continuous along a differentiable trajectory. -/
def Term.continuous (bd : Boundary) : Term → Bool
  | .var n => bd.input n
  | .constant _ => true
  | .add a b | .mul a b => a.continuous bd && b.continuous bd
  | .neg a => a.continuous bd
  | _ => false

/-- Continuity reads only the inputs of a boundary. -/
theorem Term.continuous_congr {bd bd' : Boundary} (h : bd.input = bd'.input) (t : Term) :
    t.continuous bd = t.continuous bd' := by
  induction t with
  | var n => simp [continuous, h]
  | add a b ha hb | mul a b ha hb => simp [continuous, ha, hb]
  | neg a ha => simp [continuous, ha]
  | _ => rfl

/-- An integrand with an antiderivative along every differentiable trajectory:
continuous terms, first-order evolution derivatives of states, and their sums,
negations and literal multiples. -/
def Term.tame (c : Context) (bd : Boundary) : Term → Bool
  | .derivative a (.var y) => a == c.axis && (c.locate y).isSome
  | .add a b => a.tame c bd && b.tame c bd
  | .neg a => a.tame c bd
  | .mul a b => (a.literal.isSome && b.tame c bd) || (b.literal.isSome && a.tame c bd) ||
      (a.continuous bd && b.continuous bd)
  | t => t.continuous bd

/-- The three inverse rewrites, on the evolution axis of a context with a
boundary, and the reading of declared integral states. `I_t(D_t(x))` becomes
`x - x0` with the declared initial value `x0`; any other `I_t(X)` becomes `F`
when the boundary declares `F` as the integral of `X`. -/
def Term.cancelAtom (c : Context) : Term → Option Term
  | .derivative a (.integral b X) => c.boundary.bind fun bd =>
      if a = c.axis ∧ b = c.axis ∧ X.tame c bd = true then some X else none
  | .derivative a (.derivative a' (.integral b (.var x))) => c.boundary.bind fun bd =>
      if a = c.axis ∧ a' = c.axis ∧ b = c.axis ∧ (c.locate x).isSome = true ∧
        (bd.initial x).isSome = true then some (.derivative a (.var x)) else none
  | .integral b (.derivative a (.var x)) => c.boundary.bind fun bd =>
      (bd.initial x).bind fun q =>
        if a = c.axis ∧ b = c.axis ∧ (c.locate x).isSome = true then
          some (.add (.var x) (.neg (.constant q)))
        else none
  | .integral b X => c.boundary.bind fun bd =>
      (bd.integral X).bind fun F => if b = c.axis then some (.var F) else none
  | _ => none

/-- Apply the inverse rewrites at every atom position of a sum, product or
negation. Nothing else is touched: an integral elsewhere stays, and is rejected. -/
def Term.cancel (c : Context) : Term → Term
  | .add a b => .add (a.cancel c) (b.cancel c)
  | .mul a b => .mul (a.cancel c) (b.cancel c)
  | .neg a => .neg (a.cancel c)
  | t => (t.cancelAtom c).getD t

/-- The atoms read each rewritten shape as its rewrite does. -/
def Context.Cancels (c : Context) (atoms : Term → Option ℝ) (env : String → Option ℝ) : Prop :=
  ∀ u v, u.cancelAtom c = some v → atoms u = v.eval env (c.rates env) atoms

/-- Without a boundary nothing is rewritten, so every reading cancels. -/
theorem Context.cancels_none {c : Context} (h : c.boundary = none) (atoms : Term → Option ℝ)
    (env : String → Option ℝ) : c.Cancels atoms env := by
  intro u v hu
  unfold Term.cancelAtom at hu
  split at hu <;> simp [h] at hu

/-- A rewritten shape is a non-local atom. -/
theorem Term.cancelAtom_eval {c : Context} {u v : Term} (h : u.cancelAtom c = some v)
    (env : String → Option ℝ) (rates : List String → String → Option ℝ)
    (atoms : Term → Option ℝ) : u.eval env rates atoms = atoms u := by
  unfold Term.cancelAtom at h
  split at h <;> first | simp at h | simp [Term.eval, Term.chain]

/-- The rewrites preserve meaning wherever the atoms read them as they are
rewritten. -/
theorem Term.cancel_eval (c : Context) (t : Term) (env : String → Option ℝ)
    (atoms : Term → Option ℝ) (h : c.Cancels atoms env) :
    (t.cancel c).eval env (c.rates env) atoms = t.eval env (c.rates env) atoms := by
  induction t with
  | add a b ha hb => simp only [cancel, Term.eval, ha, hb]
  | mul a b ha hb => simp only [cancel, Term.eval, ha, hb]
  | neg a ha => simp only [cancel, Term.eval, ha]
  | var _ | constant _ | apply _ _ _ => simp [cancel, cancelAtom]
  | derivative a op _ =>
      simp only [cancel]
      cases hc : (Term.derivative a op).cancelAtom c with
      | none => rfl
      | some v => rw [Option.getD_some, ← h _ _ hc, cancelAtom_eval hc]
  | integral a op _ =>
      simp only [cancel]
      cases hc : (Term.integral a op).cancelAtom c with
      | none => rfl
      | some v => rw [Option.getD_some, ← h _ _ hc, cancelAtom_eval hc]

/-! ## Discharging the premise along a trajectory -/

/-- What the rewrites need of a whole trajectory: inputs are continuous, states
are differentiable with their derivatives as first-order chains, a state with
a declared initial value starts there, and a declared integral state is an
antiderivative of the reading of its integrand that vanishes at the start. -/
structure Trajectory.Regular (T : Trajectory) (c : Context) (bd : Boundary) : Prop where
  axis : T.axis = c.axis
  input : ∀ n, bd.input n = true → ∃ g : ℝ → ℝ, ContinuousOn g (Ici T.start) ∧
    ∀ s ∈ Ici T.start, T.base s n = some (g s)
  rate : ∀ y, (c.locate y).isSome = true → ∃ g : ℝ → ℝ, ∀ s ∈ Ici T.start,
    DifferentiableWithinAt ℝ g (Ici T.start) s ∧
      T.rates s [c.axis] y = some (derivWithin g (Ici T.start) s)
  initial : ∀ x q, (c.locate x).isSome = true → bd.initial x = some q →
    ∃ g : ℝ → ℝ, g T.start = q ∧ ∀ s ∈ Ici T.start,
      DifferentiableWithinAt ℝ g (Ici T.start) s ∧ T.base s x = some (g s) ∧
        T.rates s [c.axis] x = some (derivWithin g (Ici T.start) s)
  integral : ∀ X F, bd.integral X = some F → ∃ g : ℝ → ℝ, g T.start = 0 ∧ ∀ s ∈ Ici T.start,
    T.base s F = some (g s) ∧ ∃ x, X.along T s = some x ∧ HasDerivWithinAt g x (Ici T.start) s

/-- What the rewrites need at one time: `env` extends the inputs and its ports
read first-order chains as the trajectory does. -/
structure Trajectory.At (T : Trajectory) (c : Context) (t : ℝ) (env : String → Option ℝ) :
    Prop where
  mem : t ∈ Ici T.start
  base : Agrees (T.base t) env
  rate : ∀ y, (c.locate y).isSome = true → c.rates env [c.axis] y = T.rates t [c.axis] y

/-- A literal reads its value at every time. -/
private theorem Term.along_literal {t : Term} {q : ℚ} (h : t.literal = some q) (T : Trajectory)
    (s : ℝ) : t.along T s = some (q : ℝ) := by
  induction t generalizing q with
  | constant c => cases h; rfl
  | neg a ha =>
      cases hA : a.literal <;> simp [literal, hA] at h
      subst h
      simp [Term.along, ha hA]
  | mul a b ha hb =>
      cases hA : a.literal <;> cases hB : b.literal <;> simp [literal, hA, hB] at h
      subst h
      simp [Term.along, ha hA, hb hB]
  | _ => simp [literal] at h

/-- A continuous term reads a continuous function on the half-line. -/
private theorem Term.continuous_along {bd : Boundary} {c : Context} {T : Trajectory} {t : Term}
    (h : t.continuous bd = true) (reg : T.Regular c bd) :
    ∃ g : ℝ → ℝ, ContinuousOn g (Ici T.start) ∧ ∀ s ∈ Ici T.start, t.along T s = some (g s) := by
  induction t with
  | var n => exact reg.input n h
  | constant q => exact ⟨fun _ => q, continuousOn_const, fun _ _ => rfl⟩
  | add a b ha hb =>
      simp only [continuous, Bool.and_eq_true] at h
      obtain ⟨f, hf, hfa⟩ := ha h.1
      obtain ⟨g, hg, hgb⟩ := hb h.2
      exact ⟨fun s => f s + g s, hf.add hg, fun s hs => by simp [Term.along, hfa s hs, hgb s hs]⟩
  | mul a b ha hb =>
      simp only [continuous, Bool.and_eq_true] at h
      obtain ⟨f, hf, hfa⟩ := ha h.1
      obtain ⟨g, hg, hgb⟩ := hb h.2
      exact ⟨fun s => f s * g s, hf.mul hg, fun s hs => by simp [Term.along, hfa s hs, hgb s hs]⟩
  | neg a ha =>
      obtain ⟨f, hf, hfa⟩ := ha h
      exact ⟨fun s => -f s, hf.neg, fun s hs => by simp [Term.along, hfa s hs]⟩
  | _ => simp [continuous] at h

/-- A continuous term reads the same through `env` as along the trajectory at
`t`, wherever `env` extends the trajectory's names at `t` and every input has a
value there. -/
theorem Term.continuous_agrees_at {bd : Boundary} {T : Trajectory} {t : ℝ}
    {env : String → Option ℝ} {u : Term} (h : u.continuous bd = true)
    (input : ∀ n, bd.input n = true → (T.base t n).isSome = true) (base : Agrees (T.base t) env)
    (rates : List String → String → Option ℝ) (atoms : Term → Option ℝ) :
    u.eval env rates atoms = u.along T t := by
  induction u with
  | var n =>
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (input n h)
      rw [Term.eval, Term.along, hw]
      exact base n _ hw
  | constant q => rfl
  | add a b ha hb =>
      simp only [continuous, Bool.and_eq_true] at h
      simp only [Term.eval, Term.along, ha h.1, hb h.2]
  | mul a b ha hb =>
      simp only [continuous, Bool.and_eq_true] at h
      simp only [Term.eval, Term.along, ha h.1, hb h.2]
  | neg a ha => simp only [Term.eval, Term.along, ha h]
  | _ => simp [continuous] at h

/-- A continuous term reads the same at `t` through `env` as along the trajectory. -/
private theorem Term.continuous_agrees {bd : Boundary} {c : Context} {T : Trajectory} {t : ℝ}
    {env : String → Option ℝ} {u : Term} (h : u.continuous bd = true) (reg : T.Regular c bd)
    (hat : T.At c t env) (rates : List String → String → Option ℝ) (atoms : Term → Option ℝ) :
    u.eval env rates atoms = u.along T t :=
  continuous_agrees_at h (fun n hn => by
    obtain ⟨g, -, hg⟩ := reg.input n hn
    simp [hg t hat.mem]) hat.base rates atoms

/-- A tame term reads the same at `t` through `env` as along the trajectory. -/
private theorem Term.tame_agrees {bd : Boundary} {c : Context} {T : Trajectory} {t : ℝ}
    {env : String → Option ℝ} {u : Term} (h : u.tame c bd = true) (reg : T.Regular c bd)
    (hat : T.At c t env) (atoms : Term → Option ℝ) :
    u.eval env (c.rates env) atoms = u.along T t := by
  induction u with
  | var _ | constant _ => exact continuous_agrees h reg hat _ _
  | add a b ha hb =>
      simp only [tame, Bool.and_eq_true] at h
      simp only [Term.eval, Term.along, ha h.1, hb h.2]
  | neg a ha => simp only [Term.eval, Term.along, ha h]
  | mul a b ha hb =>
      simp only [tame, Bool.or_eq_true, Bool.and_eq_true, Option.isSome_iff_exists] at h
      rcases h with (⟨⟨q, hq⟩, hb'⟩ | ⟨⟨q, hq⟩, ha'⟩) | ⟨ca, cb⟩
      · simp only [Term.eval, Term.along, hb hb', a.literal_correct q hq, a.along_literal hq]
      · simp only [Term.eval, Term.along, ha ha', b.literal_correct q hq, b.along_literal hq]
      · simp only [Term.eval, Term.along, continuous_agrees ca reg hat,
          continuous_agrees cb reg hat]
  | apply _ _ _ | integral _ _ => simp [tame, continuous] at h
  | derivative a op _ =>
      cases op with
      | var y =>
          simp only [tame, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨rfl, hy⟩ := h
          simp only [Term.eval, Term.along, Term.chain]
          exact hat.rate y hy
      | _ => simp [tame, continuous] at h

/-- A continuous integrand has an antiderivative from the start. -/
private theorem Term.continuous_primitive {bd : Boundary} {c : Context} {T : Trajectory} {u : Term}
    (h : u.continuous bd = true) (reg : T.Regular c bd) :
    ∃ F g : ℝ → ℝ, F T.start = 0 ∧ ∀ s ∈ Ici T.start, u.along T s = some (g s) ∧
      HasDerivWithinAt F (g s) (Ici T.start) s := by
  obtain ⟨g, hg, hu⟩ := continuous_along h reg
  obtain ⟨F, h0, hF, -⟩ := exists_primitive_of_continuousOn hg
  exact ⟨F, g, h0, fun s hs => ⟨hu s hs, hF s hs⟩⟩

/-- A tame integrand has an antiderivative from the start along a regular trajectory. -/
theorem Term.tame_primitive {bd : Boundary} {c : Context} {T : Trajectory} {u : Term}
    (h : u.tame c bd = true) (reg : T.Regular c bd) :
    ∃ F g : ℝ → ℝ, F T.start = 0 ∧ ∀ s ∈ Ici T.start, u.along T s = some (g s) ∧
      HasDerivWithinAt F (g s) (Ici T.start) s := by
  induction u with
  | var _ | constant _ => exact continuous_primitive h reg
  | add a b ha hb =>
      simp only [tame, Bool.and_eq_true] at h
      obtain ⟨F, f, hF0, hF⟩ := ha h.1
      obtain ⟨G, g, hG0, hG⟩ := hb h.2
      refine ⟨fun s => F s + G s, fun s => f s + g s, by simp [hF0, hG0], fun s hs => ?_⟩
      obtain ⟨hfa, hfd⟩ := hF s hs
      obtain ⟨hgb, hgd⟩ := hG s hs
      exact ⟨by simp [Term.along, hfa, hgb], hfd.add hgd⟩
  | neg a ha =>
      obtain ⟨F, f, hF0, hF⟩ := ha h
      refine ⟨fun s => -F s, fun s => -f s, by simp [hF0], fun s hs => ?_⟩
      obtain ⟨hfa, hfd⟩ := hF s hs
      exact ⟨by simp [Term.along, hfa], hfd.neg⟩
  | mul a b ha hb =>
      simp only [tame, Bool.or_eq_true, Bool.and_eq_true, Option.isSome_iff_exists] at h
      rcases h with (⟨⟨q, hq⟩, hb'⟩ | ⟨⟨q, hq⟩, ha'⟩) | ⟨ca, cb⟩
      · obtain ⟨F, f, hF0, hF⟩ := hb hb'
        refine ⟨fun s => (q : ℝ) * F s, fun s => q * f s, by simp [hF0], fun s hs => ?_⟩
        obtain ⟨hfa, hfd⟩ := hF s hs
        exact ⟨by simp [Term.along, hfa, a.along_literal hq], hfd.const_mul _⟩
      · obtain ⟨F, f, hF0, hF⟩ := ha ha'
        refine ⟨fun s => F s * q, fun s => f s * q, by simp [hF0], fun s hs => ?_⟩
        obtain ⟨hfa, hfd⟩ := hF s hs
        exact ⟨by simp [Term.along, hfa, b.along_literal hq], hfd.mul_const _⟩
      · exact continuous_primitive (by simp [continuous, ca, cb]) reg
  | apply _ _ _ | integral _ _ => simp [tame, continuous] at h
  | derivative a op _ =>
      cases op with
      | var y =>
          simp only [tame, Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨rfl, hy⟩ := h
          obtain ⟨g, hg⟩ := reg.rate y hy
          refine ⟨fun s => g s - g T.start, fun s => derivWithin g (Ici T.start) s, by simp,
            fun s hs => ⟨?_, ((hg s hs).1.hasDerivWithinAt).sub_const _⟩⟩
          simp only [Term.along, Term.chain]
          exact (hg s hs).2
      | _ => simp [tame, continuous] at h

/-- Along a regular trajectory, at a time where `env` reads inputs and ports as
the trajectory does, the trajectory reading of the atoms satisfies the premise
of `Term.cancel_eval`. -/
theorem Context.cancels {c : Context} {bd : Boundary} {T : Trajectory} {t : ℝ}
    {env : String → Option ℝ} (hb : c.boundary = some bd) (reg : T.Regular c bd)
    (hat : T.At c t env) : c.Cancels (T.atoms t) env := by
  have ht := hat.mem
  intro u v h
  unfold Term.cancelAtom at h
  split at h
  · -- `D_t(I_t(X))` becomes `X`.
    rename_i a b X
    simp only [hb, Option.bind_some] at h
    split_ifs at h with hc
    cases h
    obtain ⟨rfl, rfl, htame⟩ := hc
    obtain ⟨F, g, h0, hF⟩ := Term.tame_primitive htame reg
    rw [Trajectory.atoms, Term.tame_agrees htame reg hat, ← reg.axis]
    exact Term.along_derivative_integral h0 (fun s hs => (hF s hs).1) (fun s hs => (hF s hs).2) ht
  · -- `D_t(D_t(I_t(x)))` becomes `D_t(x)`.
    rename_i a a' b x
    simp only [hb, Option.bind_some] at h
    split_ifs at h with hc
    cases h
    obtain ⟨rfl, rfl, rfl, hl, hi⟩ := hc
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hi
    obtain ⟨g, -, hg⟩ := reg.initial x q hl hq
    obtain ⟨F, h0, hF, -⟩ := exists_primitive_of_continuousOn (g := g)
      (fun s hs => (hg s hs).1.continuousWithinAt)
    have hI : ∀ s ∈ Ici T.start, (Term.derivative c.axis (.integral c.axis (.var x))).along T s =
        some (g s) := by
      intro s hs
      rw [← reg.axis]
      rw [Term.along_derivative_integral (X := .var x) h0 (fun s hs => (hg s hs).2.1) hF hs]
      exact (hg s hs).2.1
    have houter :
        (Term.derivative c.axis (.derivative c.axis (.integral c.axis (.var x)))).along T t =
        derivFrom T.start ((Term.derivative c.axis (.integral c.axis (.var x))).along T) t := by
      rw [Term.along]
      simp only [Term.chain, Option.map_none, reg.axis, if_true]
    have hD : (Term.derivative c.axis (.var x)).eval env (c.rates env) (T.atoms t) =
        c.rates env [c.axis] x := by
      simp only [Term.eval, Term.chain]
    rw [Trajectory.atoms, houter, hD, derivFrom_eq hI ((hg t ht).1.hasDerivWithinAt) ht,
      hat.rate x hl, (hg t ht).2.2]
  · -- `I_t(D_t(x))` becomes `x - x0`.
    rename_i b a x
    simp only [hb, Option.bind_some] at h
    cases hq : bd.initial x with
    | none => simp [hq] at h
    | some q =>
      simp only [hq, Option.bind_some] at h
      split_ifs at h with hc
      cases h
      obtain ⟨rfl, rfl, hl⟩ := hc
      obtain ⟨g, g0, hg⟩ := reg.initial x q hl hq
      have := Term.along_integral_derivative (T := T) (x := x) (g := g)
        (fun s hs => ⟨(hg s hs).1, reg.axis ▸ (hg s hs).2.2⟩) ht
      rw [Trajectory.atoms, ← reg.axis, this, g0]
      have hx : env x = some (g t) := hat.base x _ (hg t ht).2.1
      simp [Term.eval, hx, sub_eq_add_neg]
  · -- A declared integral state `F` of `I_t(X)` becomes `F`.
    rename_i b X _
    simp only [hb, Option.bind_some] at h
    cases hF : bd.integral X with
    | none => simp [hF] at h
    | some F =>
      simp only [hF, Option.bind_some] at h
      split_ifs at h with hc
      cases h
      subst hc
      obtain ⟨g, g0, hg⟩ := reg.integral X F hF
      have hI : (Term.integral c.axis X).along T t = some (g t) := by
        rw [← reg.axis]
        simp only [Term.along, ite_true]
        exact primitiveFrom_iff.mpr ⟨g0, fun s hs => (hg s hs).2⟩ t ht
      rw [Trajectory.atoms, hI]
      exact (hat.base F _ (hg t ht).1).symm
  · simp at h

#print axioms Term.along_integral
#print axioms Term.along_derivative_integral
#print axioms Term.along_integral_derivative
#print axioms integral_derivative_ne
#print axioms Term.cancel_eval
#print axioms Context.cancels
#print axioms Context.cancels_none
#print axioms Term.tame_primitive
#print axioms eqOn_of_hasDerivWithinAt
#print axioms primitiveFrom_eq
#print axioms derivFrom_eq
#print axioms exists_primitive_of_continuousOn
#print axioms primitiveFrom_eq_integral
#print axioms primitiveFrom_iff
#print axioms Term.continuous_congr
#print axioms Term.continuous_agrees_at
end Gimle.Asgard.Model
