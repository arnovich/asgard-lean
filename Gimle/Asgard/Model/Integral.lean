import Gimle.Asgard.Model.Differential
import Gimle.Asgard.Model.Resolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Source integrals over the evolution axis, from the declared start, the inverse
rewrites between integrals and derivatives, and the reading of declared integral
states.

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

`Term.cancelAtom` recognizes these inverse shapes, all on the evolution axis, and
reads declared integral states (below):

- `D_t(I_t(X))` becomes `X`, when `X` is `Term.tame`: a polynomial in inputs, first-
  order state derivatives, and their sums, negations and multiples by a polynomial
  in literals and bound parameters, or an applied lambda that beta-normalizes to a
  polynomial in inputs. The derivative of the integral is the integrand
  (`Term.along_derivative_integral`). `Term.cancel` rewrites inside `X` first.
- `D_t^m(I_t(x))`, `m ≥ 2`, becomes the chain `D_t^(m-1)(x)`: the first two
  derivatives cancel the integral, and the rest differentiate `x`.
- `I_t(D_t^(k+1)(x))` becomes `y - y0`, where `y` is the state `k` declared
  velocities above `x` and `y0` its declared initial value. The boundary term is
  kept: `I_t(D_t(x))` is `x - x(start)` (`Term.along_integral_derivative`), and
  `x` alone is wrong whenever `x(start) ≠ 0` (`integral_derivative_ne`).

A chain needs every level it climbs located, with a declared initial value
(`Context.admits`); along a solution each such level is the iterated derivative of
its base (`Trajectory.Regular.iterated`).

## Declared integral states

An integral no inverse rewrite removes is read as a declared state: when the
boundary declares `F` as the integral of `X` (`Boundary.integral`), `I_t(X)`
becomes `F`. Nothing is inferred. The trajectory must make `F` the
antiderivative of the reading of `X` that vanishes at the start
(`Trajectory.Regular.integral`); then `I_t(X)` reads `F` at every time, because
the antiderivative from the start is unique (`primitiveFrom_iff`). A declaration's
own equation gives that only for a pointwise `X` (`Term.pointwise_agrees`), and an
integrand holding an integral is read through the declaration of that smaller
integral, so declarations are discharged in order of size (`Context.cancelsUpTo`).

`Term.cancel` applies them at the atom positions of a sum, product or negation, and
inside the integrand of an inverse pair. Every other integral is left in place and
rejected by lowering. The rewrite is exact wherever the atoms are read along the
trajectory (`Context.Cancels`), and `Context.cancels` discharges that premise for
every trajectory whose states are differentiable, whose ports carry the actual
derivatives, whose declared initial values hold, whose declared integral states are
antiderivatives of their integrands, whose bound parameters are constant and whose
declared velocities are the derivatives of their states: in particular, at every
time of a solution of the source or of the lowered body. -/
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
  | .unary op a, T, s => (a.along T s).bind op.partial
  | .binary op a b, T, s => do op.partial (← a.along T s) (← b.along T s)

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

/-- Every name of a named expression satisfies `p`. -/
def _root_.Gimle.Asgard.Polynomial.NamedExpr.reads (p : String → Bool) : NamedExpr → Bool
  | .var n => p n
  | .constant _ => true
  | .add a b | .mul a b => a.reads p && b.reads p
  | .neg a => a.reads p

/-- A named expression over defined inputs reads the same through any environment
that extends them. -/
theorem _root_.Gimle.Asgard.Polynomial.NamedExpr.eval_reads {e : NamedExpr}
    {p : String → Bool} {base env : String → Option ℝ} (h : e.reads p = true)
    (input : ∀ n, p n = true → (base n).isSome = true) (agrees : Agrees base env) :
    e.eval env = e.eval base := by
  induction e with
  | var n =>
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (input n h)
      simp only [NamedExpr.eval, hw]
      exact agrees n w hw
  | constant _ => rfl
  | add a b ha hb =>
      simp only [NamedExpr.reads, Bool.and_eq_true] at h
      simp only [NamedExpr.eval, ha h.1, hb h.2]
  | mul a b ha hb =>
      simp only [NamedExpr.reads, Bool.and_eq_true] at h
      simp only [NamedExpr.eval, ha h.1, hb h.2]
  | neg a ha => simp only [NamedExpr.eval, ha h]

/-- A literal reads its value at every time of every trajectory. -/
theorem Term.literal_along (t : Term) (q : ℚ) (h : t.literal = some q) (T : Trajectory)
    (s : ℝ) : t.along T s = some (q : ℝ) := by
  induction t generalizing q with
  | constant c => cases h; rfl
  | neg a ha =>
      cases hA : a.literal <;> simp [literal, hA] at h
      subst h
      simp [Term.along, ha _ hA]
  | mul a b ha hb =>
      cases hA : a.literal <;> cases hB : b.literal <;> simp [literal, hA, hB] at h
      subst h
      simp [Term.along, ha _ hA, hb _ hB]
  | binary op a b ha hb =>
      cases op <;> simp only [literal, reduceCtorEq] at h
      cases hB : b.literal with
      | none => simp [hB, Bind.bind, Option.bind] at h
      | some d =>
        by_cases hd : d = 0
        · simp [hB, hd, Bind.bind, Option.bind] at h
        · cases hA : a.literal with
          | none => simp [hB, hA, Bind.bind, Option.bind] at h
          | some n =>
            simp [hB, hA, hd, Bind.bind, Option.bind, Pure.pure] at h
            subst h
            have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
            simp [Term.along, ha _ hA, hb _ hB, RealAtomics.Binary.partial_of_domain
              (show RealAtomics.Binary.division.Domain (n : ℝ) d from hd'),
              RealAtomics.Binary.value]
  | _ => simp [literal] at h

/-- Beta normalization preserves the trajectory reading too: a lambda rebinds its
binder along the whole trajectory, and a beta-normal term has no atom. -/
theorem Term.beta_along (t : Term) (e : NamedExpr) (h : t.beta = some e) (T : Trajectory)
    (s : ℝ) : t.along T s = e.eval (T.base s) := by
  induction t generalizing e T with
  | var name => cases h; rfl
  | constant q => cases h; rfl
  | add a b ha hb =>
      cases hA : a.beta <;> cases hB : b.beta <;> simp [beta, hA, hB] at h
      subst h
      simp [NamedExpr.eval, Term.along, ha _ hA, hb _ hB]
  | mul a b ha hb =>
      cases hA : a.beta <;> cases hB : b.beta <;> simp [beta, hA, hB] at h
      subst h
      simp [NamedExpr.eval, Term.along, ha _ hA, hb _ hB]
  | neg a ha =>
      cases hA : a.beta <;> simp [beta, hA] at h
      subst h
      simp [NamedExpr.eval, Term.along, ha _ hA]
  | apply x body arg hbody harg =>
      cases hB : body.beta <;> cases hA : arg.beta <;> simp [beta, hB, hA] at h
      subst h
      rw [NamedExpr.subst_eval, Term.along, hbody _ hB]
      simp only [harg _ hA]
  | derivative _ _ _ => simp [beta] at h
  | integral _ _ _ => simp [beta] at h
  | unary _ _ _ => simp [beta] at h
  | binary op a b ha hb =>
      cases op <;> simp only [beta, reduceCtorEq] at h
      cases hB : b.literal with
      | none => simp [hB, Bind.bind, Option.bind] at h
      | some d =>
        by_cases hd : d = 0
        · simp [hB, hd, Bind.bind, Option.bind] at h
        · cases hA : a.beta with
          | none => simp [hB, hA, Bind.bind, Option.bind] at h
          | some n =>
            simp [hB, hA, hd, Bind.bind, Option.bind, Pure.pure] at h
            subst h
            have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
            rw [Term.along, b.literal_along d hB T s, ha n hA T]
            cases hn : n.eval (T.base s) <;>
              simp [NamedExpr.eval, hn, RealAtomics.Binary.partial_of_domain
                (show RealAtomics.Binary.division.Domain _ (d : ℝ) from hd'),
                RealAtomics.Binary.value, div_eq_mul_inv]

/-- A named expression as a term. -/
def _root_.Gimle.Asgard.Polynomial.NamedExpr.toTerm : NamedExpr → Term
  | .var n => .var n
  | .constant q => .constant q
  | .add a b => .add a.toTerm b.toTerm
  | .mul a b => .mul a.toTerm b.toTerm
  | .neg a => .neg a.toTerm

theorem _root_.Gimle.Asgard.Polynomial.NamedExpr.toTerm_along (e : NamedExpr) (T : Trajectory)
    (s : ℝ) : e.toTerm.along T s = e.eval (T.base s) := by
  induction e with
  | var n => rfl
  | constant q => rfl
  | add a b ha hb => simp only [NamedExpr.toTerm, Term.along, NamedExpr.eval, ha, hb]
  | mul a b ha hb => simp only [NamedExpr.toTerm, Term.along, NamedExpr.eval, ha, hb]
  | neg a ha => simp only [NamedExpr.toTerm, Term.along, NamedExpr.eval, ha]

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

theorem _root_.Gimle.Asgard.Polynomial.NamedExpr.toTerm_continuous (e : NamedExpr)
    (bd : Boundary) : e.toTerm.continuous bd = e.reads bd.input := by
  induction e with
  | var n => rfl
  | constant q => rfl
  | add a b ha hb => simp only [NamedExpr.toTerm, Term.continuous, NamedExpr.reads, ha, hb]
  | mul a b ha hb => simp only [NamedExpr.toTerm, Term.continuous, NamedExpr.reads, ha, hb]
  | neg a ha => simp only [NamedExpr.toTerm, Term.continuous, NamedExpr.reads, ha]

/-- A polynomial in bound parameters and literals, whose reading is constant along
a trajectory. -/
def Term.fixed (bd : Boundary) : Term → Bool
  | .var n => bd.parameter n
  | .constant _ => true
  | .add a b | .mul a b => a.fixed bd && b.fixed bd
  | .neg a => a.fixed bd
  | _ => false

/-- An integrand with an antiderivative along every differentiable trajectory:
continuous terms, first-order evolution derivatives of states, and their sums,
negations and multiples by a polynomial in literals and bound parameters, and
applied lambdas that beta-normalize to a continuous term. -/
def Term.tame (c : Context) (bd : Boundary) : Term → Bool
  | .derivative a (.var y) => a == c.axis && (c.locate y).isSome
  | .add a b => a.tame c bd && b.tame c bd
  | .neg a => a.tame c bd
  | .mul a b => (a.fixed bd && b.tame c bd) || (b.fixed bd && a.tame c bd) ||
      (a.continuous bd && b.continuous bd)
  | .apply x body arg => ((Term.apply x body arg).beta.map (·.reads bd.input)).getD false
  | t => t.continuous bd

/-- `D_a1(… D_ak(I_b(x)))`: the derivative axes, outermost first, the integral's
axis and `x`. -/
def Term.integralChain : Term → Option (List String × String × String)
  | .integral b (.var x) => some ([], b, x)
  | .derivative a op => op.integralChain.map fun (axes, b, x) => (a :: axes, b, x)
  | _ => none

/-- The chain `D_axes(x)`, axes outermost first. -/
def Term.ofChain : List String → String → Term
  | [], x => .var x
  | a :: axes, x => .derivative a (Term.ofChain axes x)

theorem Term.ofChain_chain (axes : List String) (x : String) :
    (Term.ofChain axes x).chain = some (axes, x) := by
  induction axes with
  | nil => rfl
  | cons a axes ih => simp [Term.ofChain, Term.chain, ih]

/-- A term holding an integral is not a chain. -/
theorem Term.integralChain_chain {t : Term} {p : List String × String × String}
    (h : t.integralChain = some p) : t.chain = none := by
  induction t generalizing p with
  | integral b op _ => rfl
  | derivative a op ih =>
      simp only [integralChain, Option.map_eq_some_iff] at h
      obtain ⟨q, hq, -⟩ := h
      simp [Term.chain, ih hq]
  | _ => simp [integralChain] at h

/-- `x` and the states `1, …, k` declared velocities above it are located and have
declared initial values: along a solution, a chain of up to `k + 1` derivatives of
`x` is then the iterated derivative of `x` (`Trajectory.Regular.iterated`). -/
def Context.admits (c : Context) (bd : Boundary) (k : Nat) (x : String) : Bool :=
  (List.range (k + 1)).all fun i => match c.lift i x with
    | some y => (c.locate y).isSome && (bd.initial y).isSome
    | none => false

theorem Context.admits_level {c : Context} {bd : Boundary} {k : Nat} {x : String}
    (h : c.admits bd k x = true) {i : Nat} (hi : i ≤ k) :
    ∃ y, c.lift i x = some y ∧ (c.locate y).isSome = true ∧ (bd.initial y).isSome = true := by
  simp only [Context.admits, List.all_eq_true, List.mem_range] at h
  have := h i (by omega)
  cases hy : c.lift i x with
  | none => simp [hy] at this
  | some y =>
      simp only [hy, Bool.and_eq_true] at this
      exact ⟨y, rfl, this⟩

/-- The inverse rewrites, on the evolution axis of a context with a boundary, and
the reading of declared integral states:

- `D_t(I_t(X))` becomes `X` for a tame `X`;
- `D_t^m(I_t(x))`, `m ≥ 2`, becomes the chain `D_t^(m-1)(x)`;
- `I_t(D_t^(k+1)(x))` becomes `y - y0`, where `y` is the state `k` declared
  velocities above `x` and `y0` its declared initial value;
- any other `I_t(X)` becomes `F` when the boundary declares `F` as the integral
  of `X`.

Chains need every level located, with a declared initial value (`Context.admits`). -/
def Term.cancelAtom (c : Context) : Term → Option Term
  | .derivative a (.integral b X) => c.boundary.bind fun bd =>
      if a = c.axis ∧ b = c.axis ∧ X.tame c bd = true then some X else none
  | .derivative a op => c.boundary.bind fun bd =>
      match op.integralChain with
      | some (axes, b, x) =>
          if (a :: axes).all (· == c.axis) = true ∧ b = c.axis ∧ axes ≠ [] ∧
              c.admits bd (axes.length - 1) x = true then some (Term.ofChain axes x)
          else none
      | none => none
  | .integral b (.derivative a op) => c.boundary.bind fun bd =>
      match op.chain with
      | some (axes, x) =>
          if (a :: axes).all (· == c.axis) = true ∧ b = c.axis ∧
              c.admits bd axes.length x = true then
            (c.lift axes.length x).bind fun y =>
              (bd.initial y).map fun q => .add (.var y) (.neg (.constant q))
          else none
      | none => (bd.integral (.derivative a op)).bind fun F =>
          if b = c.axis then some (.var F) else none
  | .integral b X => c.boundary.bind fun bd =>
      (bd.integral X).bind fun F => if b = c.axis then some (.var F) else none
  | _ => none

/-- Apply the inverse rewrites at every atom position of a sum, product or
negation, and inside the integrand of an inverse pair `D_t(I_t(X))` before trying
the pair itself. Nothing else is touched: an integral elsewhere stays, and is
rejected. -/
def Term.cancel (c : Context) : Term → Term
  | .add a b => .add (a.cancel c) (b.cancel c)
  | .mul a b => .mul (a.cancel c) (b.cancel c)
  | .neg a => .neg (a.cancel c)
  | .derivative a (.integral b X) =>
      ((Term.derivative a (.integral b (X.cancel c))).cancelAtom c).getD
        (.derivative a (.integral b X))
  | t => (t.cancelAtom c).getD t

/-- The rewrite `Term.cancel` applies at one atom: an inverse pair's after rewriting
inside its integrand, and `cancelAtom` for every other atom. -/
def Term.cancelStep (c : Context) : Term → Option Term
  | .derivative a (.integral b X) => (Term.derivative a (.integral b (X.cancel c))).cancelAtom c
  | u => u.cancelAtom c

theorem Term.cancel_derivative (c : Context) (a : String) (op : Term) :
    (Term.derivative a op).cancel c =
      ((Term.derivative a op).cancelStep c).getD (.derivative a op) := by
  cases op <;> rfl

theorem Term.cancel_integral (c : Context) (b : String) (op : Term) :
    (Term.integral b op).cancel c = ((Term.integral b op).cancelStep c).getD (.integral b op) :=
  rfl

/-- Whether a derivative or integral anywhere in the term is on another axis. -/
def Term.offAxis (axis : String) : Term → Bool
  | .var _ | .constant _ => false
  | .add a b | .mul a b => a.offAxis axis || b.offAxis axis
  | .neg a => a.offAxis axis
  | .apply _ body arg => body.offAxis axis || arg.offAxis axis
  | .derivative a op | .integral a op => a != axis || op.offAxis axis
  | .unary _ a => a.offAxis axis
  | .binary _ a b => a.offAxis axis || b.offAxis axis

/-- Why an integral is left after the rewrites, for a diagnostic: `"axis"` when the
integral, or the derivatives around or inside it, are on another axis;
`"integrand"` for an inverse pair on the evolution axis whose integrand, holding
no integral, is not tame; `"no inverse rewrite"` otherwise, such as an integral no
declaration reads, a chain whose levels have no declared velocities, or a pair
under further derivatives. The first integral in reading order is named. -/
def Term.integralReason (axis : String) : Term → Option String
  | .var _ | .constant _ => none
  | .add a b | .mul a b => (a.integralReason axis).orElse fun _ => b.integralReason axis
  | .neg a => a.integralReason axis
  | .apply _ body arg => (body.integralReason axis).orElse fun _ => arg.integralReason axis
  | .derivative a (.integral b X) =>
      some (if a != axis || b != axis || X.offAxis axis then "axis"
        else if X.integrals ≠ 0 then "no inverse rewrite" else "integrand")
  | .derivative a op =>
      if op.integrals = 0 then none
      else some (if a != axis || op.offAxis axis then "axis" else "no inverse rewrite")
  | .integral b X => some (if b != axis || X.offAxis axis then "axis" else "no inverse rewrite")
  | .unary _ a => a.integralReason axis
  | .binary _ a b => (a.integralReason axis).orElse fun _ => b.integralReason axis

/-- The atoms read each rewritten shape as its rewrite does. -/
def Context.Cancels (c : Context) (atoms : Term → Option ℝ) (env : String → Option ℝ) : Prop :=
  ∀ u v, u.cancelStep c = some v → atoms u = v.eval env (c.rates env) atoms

/-- Without a boundary nothing is rewritten, so every reading cancels. -/
theorem Context.cancels_none {c : Context} (h : c.boundary = none) (atoms : Term → Option ℝ)
    (env : String → Option ℝ) : c.Cancels atoms env := by
  intro u v hu
  unfold Term.cancelStep at hu
  split at hu <;> (unfold Term.cancelAtom at hu; split at hu <;> simp [h] at hu)

/-- A rewritten shape is a non-local atom. -/
theorem Term.cancelAtom_eval {c : Context} {u v : Term} (h : u.cancelAtom c = some v)
    (env : String → Option ℝ) (rates : List String → String → Option ℝ)
    (atoms : Term → Option ℝ) : u.eval env rates atoms = atoms u := by
  unfold Term.cancelAtom at h
  split at h
  · simp [Term.eval, Term.chain]
  · rename_i a op _
    cases hc : op.integralChain with
    | none => simp [hc] at h
    | some p => simp [Term.eval, Term.integralChain_chain hc]
  · simp [Term.eval]
  · simp [Term.eval]
  · simp at h

theorem Term.cancelStep_eval {c : Context} {u v : Term} (h : u.cancelStep c = some v)
    (env : String → Option ℝ) (rates : List String → String → Option ℝ)
    (atoms : Term → Option ℝ) : u.eval env rates atoms = atoms u := by
  unfold Term.cancelStep at h
  split at h
  · simp [Term.eval, Term.chain]
  · exact Term.cancelAtom_eval h env rates atoms

/-- Number of nodes, counting every name, literal and operator once. -/
def Term.size : Term → Nat
  | .var _ | .constant _ => 1
  | .add a b | .mul a b => a.size + b.size + 1
  | .neg a => a.size + 1
  | .apply _ body arg => body.size + arg.size + 1
  | .derivative _ op | .integral _ op => op.size + 1
  | .unary _ a => a.size + 1
  | .binary _ a b => a.size + b.size + 1

/-- The atoms read the rewritten shapes of at most `n` nodes as they are
rewritten. A declared integral state's own equation needs this only below the
size of its integrand, which is what lets nested declarations be discharged one
level at a time (`Context.cancelsUpTo`). -/
def Context.CancelsUpTo (c : Context) (n : Nat) (atoms : Term → Option ℝ)
    (env : String → Option ℝ) : Prop :=
  ∀ u v, u.size ≤ n → u.cancelStep c = some v → atoms u = v.eval env (c.rates env) atoms

theorem Context.Cancels.upTo {c : Context} {atoms : Term → Option ℝ} {env : String → Option ℝ}
    (h : c.Cancels atoms env) (n : Nat) : c.CancelsUpTo n atoms env :=
  fun u v _ hu => h u v hu

theorem Context.CancelsUpTo.mono {c : Context} {atoms : Term → Option ℝ}
    {env : String → Option ℝ} {m n : Nat} (h : c.CancelsUpTo n atoms env) (hmn : m ≤ n) :
    c.CancelsUpTo m atoms env :=
  fun u v hu => h u v (hu.trans hmn)

/-- The rewrites of a term preserve meaning wherever the atoms read its rewritten
shapes as they are rewritten; those shapes are no larger than the term. -/
theorem Term.cancel_eval_upTo (c : Context) (t : Term) (env : String → Option ℝ)
    (atoms : Term → Option ℝ) {n : Nat} (hn : t.size ≤ n) (h : c.CancelsUpTo n atoms env) :
    (t.cancel c).eval env (c.rates env) atoms = t.eval env (c.rates env) atoms := by
  induction t with
  | add a b ha hb =>
      simp only [size] at hn
      simp only [cancel, Term.eval, ha (by omega), hb (by omega)]
  | mul a b ha hb =>
      simp only [size] at hn
      simp only [cancel, Term.eval, ha (by omega), hb (by omega)]
  | neg a ha =>
      simp only [size] at hn
      simp only [cancel, Term.eval, ha (by omega)]
  | var _ | constant _ | apply _ _ _ | unary _ _ _ | binary _ _ _ _ _ =>
      simp [cancel, cancelAtom]
  | derivative a op _ =>
      rw [cancel_derivative]
      cases hc : (Term.derivative a op).cancelStep c with
      | none => rfl
      | some v => rw [Option.getD_some, ← h _ _ hn hc, cancelStep_eval hc]
  | integral a op _ =>
      rw [cancel_integral]
      cases hc : (Term.integral a op).cancelStep c with
      | none => rfl
      | some v => rw [Option.getD_some, ← h _ _ hn hc, cancelStep_eval hc]

/-- The rewrites preserve meaning wherever the atoms read them as they are
rewritten. -/
theorem Term.cancel_eval (c : Context) (t : Term) (env : String → Option ℝ)
    (atoms : Term → Option ℝ) (h : c.Cancels atoms env) :
    (t.cancel c).eval env (c.rates env) atoms = t.eval env (c.rates env) atoms :=
  t.cancel_eval_upTo c env atoms le_rfl (h.upTo _)

/-! ## Discharging the premise along a trajectory -/

/-- What the rewrites need of a whole trajectory: inputs are continuous, states
are differentiable with their derivatives as first-order chains, a state with
a declared initial value starts there, a declared integral state is an
antiderivative of the reading of its integrand that vanishes at the start, a
bound parameter is constant, and along every admitted chain of declared velocities
the states are the iterated derivatives of its base state, as the chains read. -/
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
  parameter : ∀ n, bd.parameter n = true → ∃ q : ℝ, ∀ s ∈ Ici T.start, T.base s n = some q
  iterated : ∀ x k, c.admits bd k x = true → ∃ g : ℝ → ℝ, ∀ i ≤ k, ∀ s ∈ Ici T.start,
    (c.lift i x).bind (T.base s) = some (iteratedDerivWithin i g (Ici T.start) s) ∧
    DifferentiableWithinAt ℝ (iteratedDerivWithin i g (Ici T.start)) (Ici T.start) s ∧
    T.rates s (List.replicate (i + 1) c.axis) x =
      some (iteratedDerivWithin (i + 1) g (Ici T.start) s)

/-- What the rewrites need at one time: `env` extends the inputs and its ports
read first-order chains as the trajectory does. -/
structure Trajectory.At (T : Trajectory) (c : Context) (t : ℝ) (env : String → Option ℝ) :
    Prop where
  mem : t ∈ Ici T.start
  base : Agrees (T.base t) env
  rate : ∀ y, (c.locate y).isSome = true → c.rates env [c.axis] y = T.rates t [c.axis] y

/-- A fixed term reads one value at every time of the half-line. -/
private theorem Term.fixed_along {bd : Boundary} {c : Context} {T : Trajectory} {t : Term}
    (h : t.fixed bd = true) (reg : T.Regular c bd) :
    ∃ q : ℝ, ∀ s ∈ Ici T.start, t.along T s = some q := by
  induction t with
  | var n => exact reg.parameter n h
  | constant q => exact ⟨q, fun _ _ => rfl⟩
  | add a b ha hb =>
      simp only [fixed, Bool.and_eq_true] at h
      obtain ⟨p, hp⟩ := ha h.1
      obtain ⟨q, hq⟩ := hb h.2
      exact ⟨p + q, fun s hs => by simp [Term.along, hp s hs, hq s hs]⟩
  | mul a b ha hb =>
      simp only [fixed, Bool.and_eq_true] at h
      obtain ⟨p, hp⟩ := ha h.1
      obtain ⟨q, hq⟩ := hb h.2
      exact ⟨p * q, fun s hs => by simp [Term.along, hp s hs, hq s hs]⟩
  | neg a ha =>
      obtain ⟨p, hp⟩ := ha h
      exact ⟨-p, fun s hs => by simp [Term.along, hp s hs]⟩
  | _ => simp [fixed] at h

/-- A fixed term reads the same at `t` through `env` as along the trajectory. -/
private theorem Term.fixed_agrees {bd : Boundary} {c : Context} {T : Trajectory} {t : ℝ}
    {env : String → Option ℝ} {u : Term} (h : u.fixed bd = true) (reg : T.Regular c bd)
    (hat : T.At c t env) (rates : List String → String → Option ℝ) (atoms : Term → Option ℝ) :
    u.eval env rates atoms = u.along T t := by
  induction u with
  | var n =>
      obtain ⟨q, hq⟩ := reg.parameter n h
      rw [Term.eval, Term.along, hq t hat.mem]
      exact hat.base n _ (hq t hat.mem)
  | constant q => rfl
  | add a b ha hb =>
      simp only [fixed, Bool.and_eq_true] at h
      simp only [Term.eval, Term.along, ha h.1, hb h.2]
  | mul a b ha hb =>
      simp only [fixed, Bool.and_eq_true] at h
      simp only [Term.eval, Term.along, ha h.1, hb h.2]
  | neg a ha => simp only [Term.eval, Term.along, ha h]
  | _ => simp [fixed] at h

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
      simp only [tame, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with (⟨fa, hb'⟩ | ⟨fb, ha'⟩) | ⟨ca, cb⟩
      · simp only [Term.eval, Term.along, hb hb', fixed_agrees fa reg hat]
      · simp only [Term.eval, Term.along, ha ha', fixed_agrees fb reg hat]
      · simp only [Term.eval, Term.along, continuous_agrees ca reg hat,
          continuous_agrees cb reg hat]
  | apply x body arg _ _ =>
      cases hb : (Term.apply x body arg).beta with
      | none => simp [tame, hb] at h
      | some e =>
        simp only [tame, hb, Option.map_some, Option.getD_some] at h
        rw [← (Term.apply x body arg).beta_correct e hb env _ _, Term.beta_along _ e hb T t]
        exact NamedExpr.eval_reads h (fun n hn => by
          obtain ⟨g, -, hg⟩ := reg.input n hn
          simp [hg t hat.mem]) hat.base
  | integral _ _ | unary _ _ | binary _ _ _ => simp [tame, continuous] at h
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
      simp only [tame, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with (⟨fa, hb'⟩ | ⟨fb, ha'⟩) | ⟨ca, cb⟩
      · obtain ⟨q, hq⟩ := fixed_along fa reg
        obtain ⟨F, f, hF0, hF⟩ := hb hb'
        refine ⟨fun s => q * F s, fun s => q * f s, by simp [hF0], fun s hs => ?_⟩
        obtain ⟨hfa, hfd⟩ := hF s hs
        exact ⟨by simp [Term.along, hfa, hq s hs], hfd.const_mul _⟩
      · obtain ⟨q, hq⟩ := fixed_along fb reg
        obtain ⟨F, f, hF0, hF⟩ := ha ha'
        refine ⟨fun s => F s * q, fun s => f s * q, by simp [hF0], fun s hs => ?_⟩
        obtain ⟨hfa, hfd⟩ := hF s hs
        exact ⟨by simp [Term.along, hfa, hq s hs], hfd.mul_const _⟩
      · exact continuous_primitive (by simp [continuous, ca, cb]) reg
  | apply x body arg _ _ =>
      cases hb : (Term.apply x body arg).beta with
      | none => simp [tame, hb] at h
      | some e =>
        simp only [tame, hb, Option.map_some, Option.getD_some] at h
        obtain ⟨F, g, h0, hF⟩ := continuous_primitive (u := e.toTerm)
          (by rw [NamedExpr.toTerm_continuous]; exact h) reg
        refine ⟨F, g, h0, fun s hs => ⟨?_, (hF s hs).2⟩⟩
        rw [Term.beta_along _ e hb T s, ← NamedExpr.toTerm_along]
        exact (hF s hs).1
  | integral _ _ | unary _ _ | binary _ _ _ => simp [tame, continuous] at h
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

/-! ### The rewrites along the trajectory

Each rewrite preserves the trajectory reading at every time of the half-line
(`Term.cancelAtom_along`), so rewriting inside an integrand does too
(`Term.cancel_along`), and the rewritten term reads the same at one time as along
the trajectory (`Term.cancelAtom_agrees`). Together they discharge the premise of
`Term.cancel_eval` (`Context.cancels`). -/

/-- An evolution-axis integral reads the antiderivative of its integrand. -/
theorem Term.along_integral_axis (T : Trajectory) (X : Term) (t : ℝ) :
    (Term.integral T.axis X).along T t = primitiveFrom T.start (X.along T) t := by
  simp only [Term.along, if_true]

/-- An evolution-axis derivative of a non-chain reads the derivative within the
half-line. -/
theorem Term.along_derivative_nonchain {T : Trajectory} {op : Term} (h : op.chain = none)
    (t : ℝ) : (Term.derivative T.axis op).along T t = derivFrom T.start (op.along T) t := by
  simp only [Term.along, h, if_true]

/-- The integral from the start reads only its integrand on the half-line. -/
theorem primitiveFrom_congr {start : ℝ} {f f' : ℝ → Option ℝ}
    (h : ∀ s ∈ Ici start, f s = f' s) {t : ℝ} (ht : t ∈ Ici start) :
    primitiveFrom start f t = primitiveFrom start f' t := by
  by_cases ex : ∃ F : ℝ → ℝ, F start = 0 ∧
      ∀ s ∈ Ici start, ∃ x, f s = some x ∧ HasDerivWithinAt F x (Ici start) s
  · obtain ⟨F, h0, hd⟩ := ex
    have hg : ∀ s ∈ Ici start, f s = some (derivWithin F (Ici start) s) := by
      intro s hs
      obtain ⟨x, hx, hF⟩ := hd s hs
      rw [hx, hF.derivWithin (uniqueDiffOn_Ici start s hs)]
    have hF : ∀ s ∈ Ici start,
        HasDerivWithinAt F (derivWithin F (Ici start) s) (Ici start) s := by
      intro s hs
      obtain ⟨x, hx, hF⟩ := hd s hs
      rw [hF.derivWithin (uniqueDiffOn_Ici start s hs)]
      exact hF
    rw [primitiveFrom_eq h0 hg hF ht,
      primitiveFrom_eq h0 (fun s hs => (h s hs).symm.trans (hg s hs)) hF ht]
  · have ex' : ¬ ∃ F : ℝ → ℝ, F start = 0 ∧
        ∀ s ∈ Ici start, ∃ x, f' s = some x ∧ HasDerivWithinAt F x (Ici start) s := by
      rintro ⟨F, h0, hd⟩
      exact ex ⟨F, h0, fun s hs => by rw [h s hs]; exact hd s hs⟩
    simp only [primitiveFrom, dif_neg ex, dif_neg ex']

/-- The derivative within the half-line reads only the function on the half-line. -/
theorem derivFrom_congr {start : ℝ} {f f' : ℝ → Option ℝ}
    (h : ∀ s ∈ Ici start, f s = f' s) {t : ℝ} (ht : t ∈ Ici start) :
    derivFrom start f t = derivFrom start f' t := by
  by_cases ex : ∃ g : ℝ → ℝ, (∀ s ∈ Ici start, f s = some (g s)) ∧
      DifferentiableWithinAt ℝ g (Ici start) t
  · obtain ⟨g, hg, hd⟩ := ex
    rw [derivFrom_eq hg hd.hasDerivWithinAt ht,
      derivFrom_eq (fun s hs => (h s hs).symm.trans (hg s hs)) hd.hasDerivWithinAt ht]
  · have ex' : ¬ ∃ g : ℝ → ℝ, (∀ s ∈ Ici start, f' s = some (g s)) ∧
        DifferentiableWithinAt ℝ g (Ici start) t := by
      rintro ⟨g, hg, hd⟩
      exact ex ⟨g, fun s hs => (h s hs).trans (hg s hs), hd⟩
    simp only [derivFrom, dif_neg ex, dif_neg ex']

/-- An inverse pair reads only its integrand's trajectory reading on the half-line. -/
theorem Term.along_pair_congr {T : Trajectory} {a b : String} {X Y : Term}
    (h : ∀ s ∈ Ici T.start, X.along T s = Y.along T s) {t : ℝ} (ht : t ∈ Ici T.start) :
    (Term.derivative a (.integral b X)).along T t =
      (Term.derivative a (.integral b Y)).along T t := by
  by_cases ha : a = T.axis
  · subst ha
    rw [Term.along_derivative_nonchain rfl, Term.along_derivative_nonchain rfl]
    refine derivFrom_congr (fun s hs => ?_) ht
    by_cases hb : b = T.axis
    · subst hb
      rw [Term.along_integral_axis, Term.along_integral_axis]
      exact primitiveFrom_congr h hs
    · simp [Term.along, hb]
  · simp [Term.along, Term.chain, ha]

/-- An integral chain with no derivatives is `I_b(x)`. -/
private theorem Term.integralChain_nil {op : Term} {b x : String}
    (h : op.integralChain = some ([], b, x)) : op = .integral b (.var x) := by
  cases op with
  | integral b' op' =>
      cases op' with
      | var x' =>
          simp only [integralChain, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, rfl, rfl⟩ := h
          rfl
      | _ => simp [integralChain] at h
  | derivative a op' =>
      simp only [integralChain, Option.map_eq_some_iff] at h
      obtain ⟨⟨axes, b', x'⟩, -, h⟩ := h
      simp at h
  | _ => simp [integralChain] at h

/-- Along a regular trajectory, `D_t^j(I_t(x))` reads the `(j-1)`-th iterated
derivative of `x`, given the iterated derivatives of `x` up to `k ≥ j - 2`. -/
private theorem Term.integralChain_along {c : Context} {bd : Boundary} {T : Trajectory}
    (reg : T.Regular c bd) {x : String} {k : Nat} {g : ℝ → ℝ}
    (hg : ∀ i ≤ k, ∀ s ∈ Ici T.start,
      (c.lift i x).bind (T.base s) = some (iteratedDerivWithin i g (Ici T.start) s) ∧
      DifferentiableWithinAt ℝ (iteratedDerivWithin i g (Ici T.start)) (Ici T.start) s) :
    ∀ (u : Term) (axes : List String), u.integralChain = some (axes, c.axis, x) → axes ≠ [] →
      axes.all (· == c.axis) = true → axes.length ≤ k + 2 → ∀ s ∈ Ici T.start,
        u.along T s = some (iteratedDerivWithin (axes.length - 1) g (Ici T.start) s) := by
  intro u
  induction u with
  | derivative a op ih =>
      intro axes hu hne hall hlen s hs
      simp only [integralChain, Option.map_eq_some_iff] at hu
      obtain ⟨⟨axes', b', x'⟩, hop, heq⟩ := hu
      simp only [Prod.mk.injEq] at heq
      obtain ⟨haxes, hb', hx'⟩ := heq
      rw [hb', hx'] at hop
      subst haxes
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
      obtain ⟨ha, hall'⟩ := hall
      subst ha
      have hc : op.chain = none := Term.integralChain_chain hop
      rw [← reg.axis, Term.along_derivative_nonchain hc]
      by_cases hnil : axes' = []
      · subst hnil
        have hop' := Term.integralChain_nil hop
        subst hop'
        have hbase : ∀ s ∈ Ici T.start, (Term.var x).along T s = some (g s) := by
          intro s hs
          have := (hg 0 (Nat.zero_le _) s hs).1
          simpa [Context.lift, Term.along, iteratedDerivWithin_zero] using this
        obtain ⟨F, h0, hF, -⟩ := exists_primitive_of_continuousOn (g := g) (fun s hs => by
          have := (hg 0 (Nat.zero_le _) s hs).2
          rw [iteratedDerivWithin_zero] at this
          exact this.continuousWithinAt)
        have hI : ∀ s ∈ Ici T.start,
            (Term.integral c.axis (.var x)).along T s = some (F s) := by
          intro s hs
          rw [← reg.axis, Term.along_integral_axis]
          exact primitiveFrom_eq h0 hbase hF hs
        rw [derivFrom_eq hI (hF s hs) hs]
        simp
      · have hlen' : axes'.length - 1 ≤ k := by simp at hlen; omega
        have hIH := ih axes' hop hnil hall' (by simp at hlen; omega)
        have hd := (hg _ hlen' s hs).2
        have hpos : axes'.length ≠ 0 := by simpa using hnil
        rw [derivFrom_eq (g := iteratedDerivWithin (axes'.length - 1) g (Ici T.start)) hIH
          hd.hasDerivWithinAt hs]
        simp only [List.length_cons, Nat.add_sub_cancel]
        have : axes'.length = axes'.length - 1 + 1 := by omega
        rw [this, iteratedDerivWithin_succ]
        simp only [Nat.add_sub_cancel]
  | integral b op _ =>
      intro axes hu hne
      cases op with
      | var y =>
          simp only [integralChain, Option.some.injEq, Prod.mk.injEq] at hu
          exact absurd hu.1.symm hne
      | _ => simp [integralChain] at hu
  | _ => intro axes hu; simp [integralChain] at hu

/-- Every rewrite preserves the trajectory reading at every time of the half-line. -/
theorem Term.cancelAtom_along {c : Context} {bd : Boundary} {T : Trajectory}
    (hb : c.boundary = some bd) (reg : T.Regular c bd) {u v : Term}
    (h : u.cancelAtom c = some v) {t : ℝ} (ht : t ∈ Ici T.start) :
    u.along T t = v.along T t := by
  unfold Term.cancelAtom at h
  split at h
  · -- `D_t(I_t(X))` becomes `X`.
    rename_i a b X
    simp only [hb, Option.bind_some] at h
    split_ifs at h with hc
    cases h
    obtain ⟨rfl, rfl, htame⟩ := hc
    obtain ⟨F, g, h0, hF⟩ := Term.tame_primitive htame reg
    rw [← reg.axis]
    exact Term.along_derivative_integral h0 (fun s hs => (hF s hs).1) (fun s hs => (hF s hs).2) ht
  · -- `D_t^m(I_t(x))` becomes `D_t^(m-1)(x)`.
    rename_i a op _
    simp only [hb, Option.bind_some] at h
    cases hc : op.integralChain with
    | none => simp [hc] at h
    | some p =>
      obtain ⟨axes, b, x⟩ := p
      simp only [hc] at h
      split_ifs at h with hcond
      cases h
      obtain ⟨hall, rfl, hne, hadm⟩ := hcond
      obtain ⟨g, hg⟩ := reg.iterated x _ hadm
      have hall' : axes.all (· == c.axis) = true := by
        simp only [List.all_cons, Bool.and_eq_true] at hall; exact hall.2
      have hu : (Term.derivative a op).integralChain = some (a :: axes, c.axis, x) := by
        simp only [integralChain, hc, Option.map_some]
      rw [Term.integralChain_along reg (fun i hi s hs => ⟨(hg i hi s hs).1, (hg i hi s hs).2.1⟩)
        _ _ hu (List.cons_ne_nil _ _) hall (by simp only [List.length_cons]; omega) t ht]
      have heq : axes = List.replicate axes.length c.axis := by
        simpa [List.eq_replicate_iff] using hall'
      have hlen : axes.length - 1 + 1 = axes.length := by
        have : axes.length ≠ 0 := by simpa using hne
        omega
      obtain ⟨-, -, hr⟩ := hg (axes.length - 1) le_rfl t ht
      rw [hlen] at hr
      cases axes with
      | nil => exact absurd rfl hne
      | cons a' rest =>
        simp only [Term.ofChain, Term.along, Term.ofChain_chain, List.length_cons,
          Nat.add_sub_cancel]
        rw [heq] at hr ⊢
        simpa using hr.symm
  · -- `I_t(D_t^(k+1)(x))` becomes `y - y0`, or a declared state.
    rename_i b a op
    simp only [hb, Option.bind_some] at h
    cases hc : op.chain with
    | some p =>
      obtain ⟨axes, x⟩ := p
      simp only [hc] at h
      split_ifs at h with hcond
      obtain ⟨hall, rfl, hadm⟩ := hcond
      cases hy : c.lift axes.length x with
      | none => simp [hy] at h
      | some y =>
        cases hq : bd.initial y with
        | none => simp [hy, hq] at h
        | some q =>
        simp only [hy, hq, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨g, hg⟩ := reg.iterated x _ hadm
        obtain ⟨y', hy', hloc', -⟩ := Context.admits_level hadm (le_refl axes.length)
        rw [hy, Option.some.injEq] at hy'
        subst hy'
        obtain ⟨gy, gy0, hgy⟩ := reg.initial _ q hloc' hq
        have hbase : ∀ s ∈ Ici T.start,
            T.base s y = some (iteratedDerivWithin axes.length g (Ici T.start) s) := by
          intro s hs
          simpa [hy] using (hg axes.length le_rfl s hs).1
        have heq : a :: axes = List.replicate (axes.length + 1) c.axis := by
          simpa [List.eq_replicate_iff] using hall
        have hrates : ∀ s ∈ Ici T.start, (Term.derivative a op).along T s =
            some (derivWithin (iteratedDerivWithin axes.length g (Ici T.start)) (Ici T.start)
              s) := by
          intro s hs
          have hch : (Term.derivative a op).along T s = T.rates s (a :: axes) x := by
            simp only [Term.along, hc]
          rw [hch, heq, (hg axes.length le_rfl s hs).2.2, iteratedDerivWithin_succ]
        have hstart : iteratedDerivWithin axes.length g (Ici T.start) T.start = q := by
          have h1 := hbase T.start self_mem_Ici
          rw [(hgy T.start self_mem_Ici).2.1, gy0, Option.some.injEq] at h1
          exact h1.symm
        rw [← reg.axis, Term.along_integral_axis]
        rw [primitiveFrom_eq (F := fun s => iteratedDerivWithin axes.length g (Ici T.start) s -
            iteratedDerivWithin axes.length g (Ici T.start) T.start)
          (by simp) hrates
          (fun s hs => ((hg axes.length le_rfl s hs).2.1.hasDerivWithinAt).sub_const _) ht,
          hstart]
        simp [Term.along, hbase t ht, sub_eq_add_neg]
    | none =>
      simp only [hc] at h
      cases hF : bd.integral (.derivative a op) with
      | none => simp [hF] at h
      | some F =>
        simp only [hF, Option.bind_some] at h
        split_ifs at h with hbx
        cases h
        subst hbx
        obtain ⟨g, g0, hg⟩ := reg.integral _ F hF
        rw [← reg.axis, Term.along_integral_axis,
          primitiveFrom_iff.mpr ⟨g0, fun s hs => (hg s hs).2⟩ t ht]
        exact (hg t ht).1.symm
  · -- A declared integral state `F` of `I_t(X)` becomes `F`.
    rename_i b X _
    simp only [hb, Option.bind_some] at h
    cases hF : bd.integral X with
    | none => simp [hF] at h
    | some F =>
      simp only [hF, Option.bind_some] at h
      split_ifs at h with hbx
      cases h
      subst hbx
      obtain ⟨g, g0, hg⟩ := reg.integral X F hF
      rw [← reg.axis, Term.along_integral_axis,
        primitiveFrom_iff.mpr ⟨g0, fun s hs => (hg s hs).2⟩ t ht]
      exact (hg t ht).1.symm
  · simp at h

/-- A rewritten term reads the same at one time as along the trajectory. -/
theorem Term.cancelAtom_agrees {c : Context} {bd : Boundary} {T : Trajectory} {t : ℝ}
    {env : String → Option ℝ} (hb : c.boundary = some bd) (reg : T.Regular c bd)
    (hat : T.At c t env) {u v : Term} (h : u.cancelAtom c = some v) :
    v.eval env (c.rates env) (T.atoms t) = v.along T t := by
  have ht := hat.mem
  unfold Term.cancelAtom at h
  split at h
  · rename_i a b X
    simp only [hb, Option.bind_some] at h
    split_ifs at h with hc
    cases h
    exact Term.tame_agrees hc.2.2 reg hat _
  · rename_i a op _
    simp only [hb, Option.bind_some] at h
    cases hc : op.integralChain with
    | none => simp [hc] at h
    | some p =>
      obtain ⟨axes, b, x⟩ := p
      simp only [hc] at h
      split_ifs at h with hcond
      cases h
      obtain ⟨hall, -, hne, hadm⟩ := hcond
      have hall' : axes.all (· == c.axis) = true := by
        simp only [List.all_cons, Bool.and_eq_true] at hall; exact hall.2
      have heq : axes = List.replicate axes.length c.axis := by
        simpa [List.eq_replicate_iff] using hall'
      have hpos : axes.length ≠ 0 := by simpa using hne
      obtain ⟨y, hy, hloc, hini⟩ := Context.admits_level hadm (le_refl (axes.length - 1))
      obtain ⟨g, hg⟩ := reg.iterated x _ hadm
      have hadmy : c.admits bd 0 y = true := by
        simp [Context.admits, Context.lift, hloc, hini]
      obtain ⟨gy, hgy⟩ := reg.iterated y 0 hadmy
      have eq : Set.EqOn gy (iteratedDerivWithin (axes.length - 1) g (Ici T.start))
          (Ici T.start) := by
        intro s hs
        have h1 := (hgy 0 le_rfl s hs).1
        have h2 := (hg _ le_rfl s hs).1
        rw [hy] at h2
        simp only [Context.lift, Option.bind_some, iteratedDerivWithin_zero] at h1 h2
        rw [h1, Option.some.injEq] at h2
        exact h2
      have hlen : axes.length - 1 + 1 = axes.length := by omega
      have rx := (hg _ le_rfl t ht).2.2
      rw [hlen] at rx
      have ry := (hgy 0 le_rfl t ht).2.2
      have along : (Term.ofChain axes x).along T t = T.rates t axes x := by
        cases axes with
        | nil => exact absurd rfl hne
        | cons a' rest => simp [Term.ofChain, Term.along, Term.ofChain_chain]
      have eval :
          (Term.ofChain axes x).eval env (c.rates env) (T.atoms t) = c.rates env axes x := by
        cases axes with
        | nil => exact absurd rfl hne
        | cons a' rest => simp [Term.ofChain, Term.eval, Term.ofChain_chain]
      rw [eval, along]
      have lhs : c.rates env axes x = c.rates env [c.axis] y := by
        conv_lhs => rw [heq]
        simp [Context.rates, hpos, Context.lift, hy]
      rw [lhs, hat.rate y hloc]
      simp only [zero_add, List.replicate_one, iteratedDerivWithin_one] at ry
      rw [ry]
      conv_rhs => rw [heq]
      rw [rx, Option.some.injEq, ← hlen, iteratedDerivWithin_succ]
      exact derivWithin_congr eq (eq ht)
  · -- `y - y0` or a declared state.
    rename_i b a op
    simp only [hb, Option.bind_some] at h
    cases hc : op.chain with
    | some p =>
      obtain ⟨axes, x⟩ := p
      simp only [hc] at h
      split_ifs at h with hcond
      obtain ⟨-, -, hadm⟩ := hcond
      cases hy : c.lift axes.length x with
      | none => simp [hy] at h
      | some y =>
        cases hq : bd.initial y with
        | none => simp [hy, hq] at h
        | some q =>
        simp only [hy, hq, Option.bind_some, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨g, hg⟩ := reg.iterated x _ hadm
        have hbase : T.base t y = some (iteratedDerivWithin axes.length g (Ici T.start) t) := by
          simpa [hy] using (hg axes.length le_rfl t ht).1
        simp [Term.eval, Term.along, hbase, hat.base y _ hbase]
    | none =>
      simp only [hc] at h
      cases hF : bd.integral (.derivative a op) with
      | none => simp [hF] at h
      | some F =>
        simp only [hF, Option.bind_some] at h
        split_ifs at h with hbx
        cases h
        obtain ⟨g, -, hg⟩ := reg.integral _ F hF
        simp only [Term.eval, Term.along]
        rw [(hg t ht).1]
        exact hat.base F _ (hg t ht).1
  · rename_i b X _
    simp only [hb, Option.bind_some] at h
    cases hF : bd.integral X with
    | none => simp [hF] at h
    | some F =>
      simp only [hF, Option.bind_some] at h
      split_ifs at h with hbx
      cases h
      obtain ⟨g, -, hg⟩ := reg.integral X F hF
      simp only [Term.eval, Term.along]
      rw [(hg t ht).1]
      exact hat.base F _ (hg t ht).1
  · simp at h

/-- Rewriting preserves the trajectory reading at every time of the half-line,
inside integrands too. -/
theorem Term.cancel_along {c : Context} {bd : Boundary} {T : Trajectory}
    (hb : c.boundary = some bd) (reg : T.Regular c bd) (u : Term) :
    ∀ s ∈ Ici T.start, (u.cancel c).along T s = u.along T s := by
  suffices key : ∀ n (u : Term), u.size ≤ n → ∀ s ∈ Ici T.start,
      (u.cancel c).along T s = u.along T s from key _ u le_rfl
  intro n
  induction n with
  | zero => intro u hu; cases u <;> simp [Term.size] at hu
  | succ n ih =>
    intro u hu s hs
    cases u with
    | add a b =>
        simp only [Term.size] at hu
        simp only [Term.cancel, Term.along, ih a (by omega) s hs, ih b (by omega) s hs]
    | mul a b =>
        simp only [Term.size] at hu
        simp only [Term.cancel, Term.along, ih a (by omega) s hs, ih b (by omega) s hs]
    | neg a =>
        simp only [Term.size] at hu
        simp only [Term.cancel, Term.along, ih a (by omega) s hs]
    | var _ | constant _ | apply _ _ _ | unary _ _ | binary _ _ _ =>
      simp [Term.cancel, Term.cancelAtom]
    | integral b op =>
        rw [Term.cancel_integral]
        cases hc : (Term.integral b op).cancelStep c with
        | none => rfl
        | some v =>
          rw [Option.getD_some]
          exact (Term.cancelAtom_along hb reg (by simpa [Term.cancelStep] using hc) hs).symm
    | derivative a op =>
        rw [Term.cancel_derivative]
        cases hc : (Term.derivative a op).cancelStep c with
        | none => rfl
        | some v =>
          rw [Option.getD_some]
          cases op
          case integral b X =>
            simp only [Term.cancelStep] at hc
            simp only [Term.size] at hu
            rw [← Term.cancelAtom_along hb reg hc hs]
            exact Term.along_pair_congr (fun s' hs' => ih X (by omega) s' hs') hs
          all_goals
            exact (Term.cancelAtom_along hb reg (by simpa [Term.cancelStep] using hc) hs).symm

/-- Along a regular trajectory, at a time where `env` reads inputs and ports as
the trajectory does, the trajectory reading of the atoms satisfies the premise
of `Term.cancel_eval`. -/
theorem Context.cancels {c : Context} {bd : Boundary} {T : Trajectory} {t : ℝ}
    {env : String → Option ℝ} (hb : c.boundary = some bd) (reg : T.Regular c bd)
    (hat : T.At c t env) : c.Cancels (T.atoms t) env := by
  intro u v h
  unfold Term.cancelStep at h
  split at h
  · rename_i a b X
    rw [Trajectory.atoms, Term.along_pair_congr (Y := X.cancel c)
      (fun s hs => (Term.cancel_along hb reg X s hs).symm) hat.mem,
      Term.cancelAtom_along hb reg h hat.mem]
    exact (Term.cancelAtom_agrees hb reg hat h).symm
  · rw [Trajectory.atoms, Term.cancelAtom_along hb reg h hat.mem]
    exact (Term.cancelAtom_agrees hb reg hat h).symm

/-! ## Pointwise integrands

A declared integral state `F` of `I_t(X)` is read through its own equation
`D_t(F) = X` at each time. That makes `F` the antiderivative of the trajectory
reading of `X` only where the one-time reading of `X` agrees with its trajectory
reading. It does for every `Term.pointwise` term: polynomials in inputs, first-order
evolution derivatives of states (read through the ports), every integral and every
derivative of a non-chain (both are atoms, read along the trajectory by
definition), and applied lambdas that beta-normalize to a polynomial in inputs. A
name that is not an input, such as an auxiliary, has no trajectory reading, and a
higher-order chain is read through velocities that only a solution ties to the
iterated derivative, so neither is pointwise. -/

/-- A term whose reading at one time, through an environment that extends the
trajectory's inputs and ports at that time and reads atoms along the trajectory,
is its trajectory reading (`Term.pointwise_agrees`). `axis` and `locate` are those
of the context, and `input` the boundary's. -/
def Term.pointwise (axis : String) (locate : String → Option String) (input : String → Bool) :
    Term → Bool
  | .var n => input n
  | .constant _ => true
  | .add a b | .mul a b => a.pointwise axis locate input && b.pointwise axis locate input
  | .neg a => a.pointwise axis locate input
  | .apply x body arg => ((Term.apply x body arg).beta.map (·.reads input)).getD false
  | .derivative a op =>
      match op with
      | .var y => a == axis && (locate y).isSome
      | _ => op.chain.isNone
  | .integral _ _ => true
  | .unary _ _ | .binary _ _ _ => false

/-- A pointwise term reads the same at `t` through `env` as along the trajectory,
wherever `env` extends the trajectory's inputs at `t`, every input has a value there
and the ports read first-order chains as the trajectory does. -/
theorem Term.pointwise_agrees {c : Context} {input : String → Bool} {T : Trajectory} {t : ℝ}
    {env : String → Option ℝ} {u : Term} (h : u.pointwise c.axis c.locate input = true)
    (hinput : ∀ n, input n = true → (T.base t n).isSome = true) (base : Agrees (T.base t) env)
    (rate : ∀ y, (c.locate y).isSome = true → c.rates env [c.axis] y = T.rates t [c.axis] y) :
    u.eval env (c.rates env) (T.atoms t) = u.along T t := by
  induction u with
  | var n =>
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hinput n h)
      rw [Term.eval, Term.along, hw]
      exact base n _ hw
  | constant _ => rfl
  | add a b ha hb =>
      simp only [pointwise, Bool.and_eq_true] at h
      simp only [Term.eval, Term.along, ha h.1, hb h.2]
  | mul a b ha hb =>
      simp only [pointwise, Bool.and_eq_true] at h
      simp only [Term.eval, Term.along, ha h.1, hb h.2]
  | neg a ha => simp only [Term.eval, Term.along, ha h]
  | integral _ _ _ => rfl
  | unary _ _ _ | binary _ _ _ _ _ => simp [pointwise] at h
  | apply x body arg _ _ =>
      cases hb : (Term.apply x body arg).beta with
      | none => simp [pointwise, hb] at h
      | some e =>
        simp only [pointwise, hb, Option.map_some, Option.getD_some] at h
        rw [← (Term.apply x body arg).beta_correct e hb env _ _, Term.beta_along _ e hb T t]
        exact NamedExpr.eval_reads h hinput base
  | derivative a op _ =>
      by_cases hv : ∃ y, op = .var y
      · obtain ⟨y, rfl⟩ := hv
        simp only [pointwise, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨rfl, hy⟩ := h
        simp only [Term.eval, Term.along, Term.chain]
        exact rate y hy
      · have hc : op.chain = none := by
          cases op with
          | var y => exact absurd ⟨y, rfl⟩ hv
          | _ => simpa [pointwise] using h
        simp only [Term.eval, hc, Trajectory.atoms]

/-! ## Declared integral states below a size

`Boundary.below n` keeps only the declared integral states of integrands with
fewer than `n` nodes. Along a trajectory whose declarations below `n` hold, the
atoms of at most `n` nodes read the rewrites (`Context.cancelsUpTo`), which is all
that a declaration with an integrand of `n` nodes needs. -/

/-- The boundary with the integral states of integrands with fewer than `n` nodes. -/
def Boundary.below (bd : Boundary) (n : Nat) : Boundary :=
  { bd with integral := fun X => if X.size < n then bd.integral X else none }

/-- The context with only the integral states below `n`. -/
def Context.below (c : Context) (n : Nat) : Context :=
  { c with boundary := c.boundary.map (·.below n) }

/-- Fixedness reads only the bound parameters. -/
theorem Term.fixed_congr {bd bd' : Boundary} (h : bd.parameter = bd'.parameter) (t : Term) :
    t.fixed bd = t.fixed bd' := by
  induction t with
  | var n => simp [fixed, h]
  | add a b ha hb | mul a b ha hb => simp [fixed, ha, hb]
  | neg a ha => simp [fixed, ha]
  | _ => rfl

/-- Tameness reads only the axis, the located states, the inputs and the bound
parameters. -/
theorem Term.tame_congr {c c' : Context} {bd bd' : Boundary} (ha : c.axis = c'.axis)
    (hl : c.locate = c'.locate) (hi : bd.input = bd'.input) (hp : bd.parameter = bd'.parameter)
    (t : Term) : t.tame c bd = t.tame c' bd' := by
  induction t with
  | var _ | constant _ => simp [tame, Term.continuous_congr hi]
  | add a b ha' hb' => simp [tame, ha', hb']
  | neg a ha' => simp [tame, ha']
  | mul a b ha' hb' => simp [tame, ha', hb', Term.continuous_congr hi, Term.fixed_congr hp]
  | apply _ _ _ _ _ => simp [tame, hi]
  | integral _ _ _ => simp [tame, Term.continuous_congr hi]
  | unary _ _ _ | binary _ _ _ _ _ => rfl
  | derivative a op _ =>
      cases op <;> simp [tame, ha, hl, Term.continuous_congr hi]

theorem Context.below_lift (c : Context) (n k : Nat) (x : String) :
    (c.below n).lift k x = c.lift k x := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Context.lift, ih]; rfl

theorem Context.admits_below (c : Context) (n : Nat) (bd : Boundary) (k : Nat) (x : String) :
    (c.below n).admits bd k x = c.admits bd k x := by
  simp only [Context.admits, Context.below_lift]
  rfl

/-- On shapes of at most `n` nodes the restricted context rewrites as the full one. -/
theorem Term.cancelAtom_below {c : Context} {n : Nat} {u : Term} (hu : u.size ≤ n) :
    u.cancelAtom (c.below n) = u.cancelAtom c := by
  have tame := fun (bd : Boundary) (X : Term) =>
    Term.tame_congr (c := c.below n) (c' := c) (bd := bd.below n) (bd' := bd) rfl rfl rfl rfl X
  cases hb : c.boundary with
  | none =>
      have hb' : (c.below n).boundary = none := by simp [Context.below, hb]
      unfold Term.cancelAtom
      split <;> simp [hb, hb']
  | some bd =>
      have hb' : (c.below n).boundary = some (bd.below n) := by simp [Context.below, hb]
      unfold Term.cancelAtom
      split
      · simp only [hb, hb', Option.bind_some, tame]; rfl
      · simp only [hb, hb', Option.bind_some, Context.admits_below]
        rfl
      · rename_i b a op
        simp only [hb, hb', Option.bind_some, Context.admits_below, Context.below_lift]
        split
        · rfl
        · simp only [size] at hu
          simp only [Boundary.below, if_pos (show (Term.derivative a op).size < n by
            simp only [size]; omega)]
          rfl
      · rename_i b X _
        simp only [size] at hu
        simp only [hb, hb', Option.bind_some, Boundary.below, if_pos (show X.size < n by omega)]
        rfl
      · rfl

/-- An inverse pair reads no declared integral state, so the restricted context
rewrites it as the full one whatever its size. -/
theorem Term.cancelAtom_pair_below (c : Context) (n : Nat) (a b : String) (Y : Term) :
    (Term.derivative a (.integral b Y)).cancelAtom (c.below n) =
      (Term.derivative a (.integral b Y)).cancelAtom c := by
  have tame := fun (bd : Boundary) (X : Term) =>
    Term.tame_congr (c := c.below n) (c' := c) (bd := bd.below n) (bd' := bd) rfl rfl rfl rfl X
  cases hb : c.boundary with
  | none =>
      have hb' : (c.below n).boundary = none := by simp [Context.below, hb]
      simp [Term.cancelAtom, hb, hb']
  | some bd =>
      have hb' : (c.below n).boundary = some (bd.below n) := by simp [Context.below, hb]
      simp only [Term.cancelAtom, hb, hb', Option.bind_some, tame]
      rfl

/-- On terms of at most `n` nodes the restricted context rewrites as the full one. -/
theorem Term.cancel_below {c : Context} {n : Nat} :
    ∀ u : Term, u.size ≤ n →
      u.cancel (c.below n) = u.cancel c ∧ u.cancelStep (c.below n) = u.cancelStep c := by
  suffices key : ∀ m (u : Term), u.size ≤ m → m ≤ n →
      u.cancel (c.below n) = u.cancel c ∧ u.cancelStep (c.below n) = u.cancelStep c from
    fun u hu => key _ u le_rfl hu
  intro m
  induction m with
  | zero => intro u hu; cases u <;> simp [Term.size] at hu
  | succ m ih =>
    intro u hu hm
    have step : u.cancelStep (c.below n) = u.cancelStep c := by
      unfold Term.cancelStep
      split
      · rename_i a b X
        simp only [size] at hu
        rw [(ih X (by omega) (by omega)).1, Term.cancelAtom_pair_below]
      · exact Term.cancelAtom_below (hu.trans hm)
    refine ⟨?_, step⟩
    cases u with
    | add a b =>
        simp only [size] at hu
        simp only [Term.cancel, (ih a (by omega) (by omega)).1, (ih b (by omega) (by omega)).1]
    | mul a b =>
        simp only [size] at hu
        simp only [Term.cancel, (ih a (by omega) (by omega)).1, (ih b (by omega) (by omega)).1]
    | neg a =>
        simp only [size] at hu
        simp only [Term.cancel, (ih a (by omega) (by omega)).1]
    | var _ | constant _ | apply _ _ _ | unary _ _ | binary _ _ _ =>
      simp [Term.cancel, Term.cancelAtom]
    | derivative a op => rw [Term.cancel_derivative, Term.cancel_derivative, step]
    | integral b op => rw [Term.cancel_integral, Term.cancel_integral, step]

/-- The restriction reads chains as the full context does. -/
theorem Context.below_rates (c : Context) (n : Nat) {α : Type} (env : String → Option α) :
    (c.below n).rates env = c.rates env := by
  funext axes x
  simp only [Context.rates, Context.below_lift]
  rfl

/-- A trajectory regular for a context is regular for its restriction. -/
theorem Trajectory.Regular.toBelow {T : Trajectory} {c : Context} {bd : Boundary} (n : Nat)
    (reg : T.Regular c bd) : T.Regular (c.below n) bd where
  axis := reg.axis
  input := reg.input
  rate := reg.rate
  initial := reg.initial
  integral := reg.integral
  parameter := reg.parameter
  iterated x k h := by
    rw [Context.admits_below] at h
    obtain ⟨g, hg⟩ := reg.iterated x k h
    exact ⟨g, fun i hi s hs => by rw [Context.below_lift]; exact hg i hi s hs⟩

/-- Along a trajectory regular for the integral states below `n`, the atoms of at
most `n` nodes read the rewrites of the full context. -/
theorem Context.cancelsUpTo {c : Context} {bd : Boundary} {T : Trajectory} {t : ℝ}
    {env : String → Option ℝ} (n : Nat) (hb : c.boundary = some bd)
    (reg : T.Regular c (bd.below n)) (hat : T.At c t env) :
    c.CancelsUpTo n (T.atoms t) env := by
  have hb' : (c.below n).boundary = some (bd.below n) := by simp [Context.below, hb]
  have hat' : T.At (c.below n) t env :=
    ⟨hat.mem, hat.base, fun y hy => by rw [c.below_rates]; exact hat.rate y hy⟩
  have cancels := Context.cancels hb' (reg.toBelow n) hat'
  intro u v hu h
  rw [← (Term.cancel_below u hu).2] at h
  rw [cancels u v h, c.below_rates]

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
#print axioms Term.cancel_eval_upTo
#print axioms Term.beta_along
#print axioms Term.pointwise_agrees
#print axioms Term.cancelAtom_below
#print axioms Term.cancel_below
#print axioms Term.cancel_along
#print axioms Term.cancelAtom_along
#print axioms Term.cancelAtom_agrees
#print axioms Context.cancelsUpTo
end Gimle.Asgard.Model
