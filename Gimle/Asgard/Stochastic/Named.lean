import Gimle.Asgard.Stochastic.Circuit
import Gimle.Asgard.Dynamics.Named

/-! Named polynomial coefficient source, checked resolution, and compilation to
process integral banks. Source evaluation never runs a target circuit. -/
namespace Gimle.Asgard.Stochastic
open Polynomial
open scoped BigOperators

abbrev Channels (w j : Nat) := Fin ((1 + w) + j)

structure NamedSystem (n d w j : Nat) where
  inputs : Fin (n + d) → Port
  noiseIds : Fin w → String
  jumpIds : Fin j → String
  axis : String
  calculus : Calculus
  jumpConvention : JumpConvention
  drift : Fin n → NamedExpr
  diffusion : Fin w → Fin n → NamedExpr
  jump : Fin j → Fin n → NamedExpr

/-- Explicit state-first, external-second interface. Names/IDs are checked;
noise and jump identifiers describe ordered process coordinates, not laws. -/
def NamedSystem.valid {n d w j : Nat} (s : NamedSystem n d w j) : Bool :=
  validPorts (List.ofFn s.inputs) && !s.axis.isEmpty &&
  decide ((List.ofFn s.noiseIds ++ List.ofFn s.jumpIds).Nodup) &&
  (List.ofFn s.noiseIds ++ List.ofFn s.jumpIds).all (fun id => !id.isEmpty) &&
  (List.ofFn (fun i : Fin n => s.inputs (Fin.castAdd d i))).all (fun p => p.role == .state) &&
  (List.ofFn (fun i : Fin d => s.inputs (Fin.natAdd n i))).all
    (fun p => p.role == .driver || p.role == .parameter)

def NamedSystem.index {n d w j : Nat} (s : NamedSystem n d w j) (name : String) :
    Option (Fin (n + d)) :=
  (lookupIndex (List.ofFn (fun i => (s.inputs i).name)) name).map (Fin.cast (by simp))

def NamedSystem.bindings {n d w j : Nat} (s : NamedSystem n d w j)
    (name : String) : Option (Expr (n + d)) := (s.index name).map Expr.var

noncomputable def NamedSystem.environment {n d w j : Nat} (s : NamedSystem n d w j)
    (x : Point (n + d)) (name : String) : Option ℝ := (s.index name).map x

def NamedSystem.kind {n d w j : Nat} (s : NamedSystem n d w j) : Channels w j → IntegralKind w j :=
  Fin.addCases (Fin.addCases (fun _ => .time) (.noise s.calculus)) (.jump s.jumpConvention)

def NamedSystem.coefficient {n d w j : Nat} (s : NamedSystem n d w j) :
    Channels w j → Fin n → NamedExpr :=
  Fin.addCases (Fin.addCases (fun _ => s.drift) s.diffusion) s.jump

/-- Itô and jump integrands read left-limit inputs. Stratonovich uses the
current process. Realizations must justify predictability and regularity. -/
def IntegralKind.predictable {w j : Nat} : IntegralKind w j → Bool
  | .time => false
  | .noise .stratonovich _ => false
  | .noise .ito _ => true
  | .jump _ _ => true

noncomputable def sample {Ω : Type} {w j n : Nat} (kind : IntegralKind w j)
    (x : Process Ω n) : Process Ω n := if kind.predictable then before x else x

def sampleAdmissible {Ω : Type} {w j n : Nat} (kind : IntegralKind w j)
    (time : Window) (x : Process Ω n) : Prop :=
  kind.predictable = true → HasLeftLimits time x

/-- Unbound source names have no value, including inside an unused coefficient. -/
def NamedSystem.Evaluates {Ω : Type} {n d w j : Nat} (s : NamedSystem n d w j)
    (time : Window) (k : Channels w j) (x : Process Ω (n + d)) (a : Process Ω n) : Prop :=
  sampleAdmissible (s.kind k) time x ∧ ∀ t ω i, (s.coefficient k i).eval (s.environment (sample (s.kind k) x t ω)) = some (a t ω i)

/-- Independent source integral equations. All coefficient processes and
integrals are named explicitly; the same drivers and sample space are shared. -/
def NamedSystem.Increments {Ω : Type} {n d w j : Nat} (s : NamedSystem n d w j)
    (ctx : Context Ω w j) (x : Process Ω (n + d)) (y : Process Ω n) : Prop :=
  s.valid = true ∧ ctx.admissible ∧ s.axis = ctx.time.axis ∧
    ∃ coefficients : Channels w j → Process Ω n,
    ∃ integrals : Channels w j → Process Ω n,
      (∀ k, s.Evaluates ctx.time k x (coefficients k)) ∧
      (∀ k i, ctx.integral (s.kind k) (fun t ω => coefficients k t ω i)
        (fun t ω => integrals k t ω i)) ∧
      y = fun t ω i => ∑ k, integrals k t ω i

/-- Initialization/evolution equations are imposed on the window. Predictable
sampling also requires a left-limit extension at its initial endpoint, and the
selected integral interpretation may impose further path conditions. Initial data
may be a random process
on the same sample space, with law assumptions in the selected context. -/
def NamedSystem.Solves {Ω : Type} {n d w j : Nat} (s : NamedSystem n d w j)
    (ctx : Context Ω w j) (u : Process Ω d) (initial : Ω → Point n)
    (x : Process Ω n) : Prop :=
  ∃ increments, s.Increments ctx (append x u) increments ∧
    (∀ ω, x ctx.time.start ω = initial ω) ∧
    ∀ t ∈ ctx.time.domain, ∀ ω i, x t ω i = initial ω i + increments t ω i

structure Prepared {n d w j : Nat} (s : NamedSystem n d w j) where
  valid : s.valid = true
  expressions : Channels w j → Fin n → Expr (n + d)
  resolved : ∀ k i, (s.coefficient k i).resolve s.bindings = some (expressions k i)

/-- Preparation checks every coefficient and rejects missing names, duplicate
ports/process IDs and wrong roles instead of supplying a default wire. -/
def NamedSystem.prepare {n d w j : Nat} (s : NamedSystem n d w j) : Option (Prepared s) :=
  if hv : s.valid = true then
    match he : Dynamics.resolveTable (fun k : Channels w j =>
      Dynamics.resolveTable (fun i : Fin n => (s.coefficient k i).resolve s.bindings)) with
    | none => none
    | some expressions => some {
        valid := hv
        expressions := expressions
        resolved := fun k => Dynamics.resolveTable_correct _ _
          (Dynamics.resolveTable_correct _ _ he k)
      }
  else none

/-- Each bank is a real typed Asgard circuit over the retained input interface. -/
def Prepared.field {n d w j : Nat} {s : NamedSystem n d w j} (p : Prepared s)
    (k : Channels w j) : Gimle.Asgard.Circuit (n + d) n := compileOutputs (p.expressions k)

def samplingCircuit {w j n : Nat} (kind : IntegralKind w j) : Circuit w j n n :=
  if kind.predictable then .before n else .lift (Wiring.identity n)

@[simp] theorem samplingCircuit_rel {Ω : Type} {w j n : Nat} (kind : IntegralKind w j)
    (ctx : Context Ω w j) (x y : Process Ω n) :
    (samplingCircuit kind).Rel ctx x y ↔ sampleAdmissible kind ctx.time x ∧ y = sample kind x := by
  simp only [samplingCircuit, sample, sampleAdmissible]
  split <;> simp_all [Circuit.Rel]

def Prepared.branch {n d w j : Nat} {s : NamedSystem n d w j} (p : Prepared s)
    (k : Channels w j) : Circuit w j (n + d) n :=
  .compose (samplingCircuit (s.kind k))
    (.compose (.lift (p.field k)) (.integrate (s.kind k) n))

/-- The result has exactly n+d inputs and n increment outputs. It contains no
feedback or initial-value insertion. Shared coefficients reuse the same input. -/
def Prepared.compile {n d w j : Nat} {s : NamedSystem n d w j} (p : Prepared s) :
    Circuit w j (n + d) n := .guard s.axis (.sum ((1 + w) + j) p.branch)

theorem Prepared.expression_correct {n d w j : Nat} {s : NamedSystem n d w j}
    (p : Prepared s) (k : Channels w j) (i : Fin n) (x : Point (n + d)) :
    (s.coefficient k i).eval (s.environment x) = some ((p.expressions k i).eval x) := by
  have h := (s.coefficient k i).resolve_correct s.bindings x
  rw [p.resolved k i] at h
  have env : (fun name => (s.bindings name).map (Expr.eval x)) = s.environment x := by
    funext name
    simp [NamedSystem.bindings, NamedSystem.environment, Option.map_map, Function.comp_def, Expr.eval]
  rw [env] at h
  exact h.symm

theorem Prepared.evaluates_iff {Ω : Type} {n d w j : Nat} {s : NamedSystem n d w j}
    (p : Prepared s) (time : Window) (k : Channels w j) (x : Process Ω (n + d)) (a : Process Ω n) :
    s.Evaluates time k x a ↔ sampleAdmissible (s.kind k) time x ∧
      a = fun t ω => (p.field k).run (sample (s.kind k) x t ω) := by
  simp only [NamedSystem.Evaluates, p.expression_correct, Option.some.injEq,
    Prepared.field, compileOutputs_correct]
  apply and_congr_right
  intro _
  constructor
  · intro h; funext t ω i; exact (h t ω i).symm
  · intro h; subst a; exact fun _ _ _ => rfl

theorem Prepared.branch_correct {Ω : Type} {n d w j : Nat} {s : NamedSystem n d w j}
    (p : Prepared s) (k : Channels w j) (ctx : Context Ω w j)
    (x : Process Ω (n + d)) (y : Process Ω n) :
    (p.branch k).Rel ctx x y ↔ ∃ a, s.Evaluates ctx.time k x a ∧
      ∀ i, ctx.integral (s.kind k) (fun t ω => a t ω i) (fun t ω => y t ω i) := by
  simp [Prepared.branch, Circuit.Rel, samplingCircuit_rel, p.evaluates_iff]

/-- Independent named evaluation equals the compiled integral-bank circuit in
both directions, for every supplied interpretation. This is a compiler theorem,
not a theorem that an arbitrary supplied relation implements stochastic calculus. -/
theorem Prepared.increments_iff_circuit {Ω : Type} {n d w j : Nat}
    {s : NamedSystem n d w j} (p : Prepared s) (ctx : Context Ω w j)
    (x : Process Ω (n + d)) (y : Process Ω n) :
    s.Increments ctx x y ↔ p.compile.Rel ctx x y := by
  simp only [NamedSystem.Increments, p.valid, true_and, Prepared.compile, Circuit.Rel]
  constructor
  · rintro ⟨ha, ht, coefficients, integrals, hc, hi, hy⟩
    exact ⟨ha, ht, integrals, fun k => (p.branch_correct k ctx x (integrals k)).mpr
      ⟨coefficients k, hc k, hi k⟩, hy⟩
  · rintro ⟨ha, ht, integrals, h, hy⟩
    have h' := fun k => (p.branch_correct k ctx x (integrals k)).mp (h k)
    choose coefficients hc hi using h'
    exact ⟨ha, ht, coefficients, integrals, hc, hi, hy⟩

/-- A convenient introduction rule retains every source sampling and integration
premise while using the already proved coefficient compiler. -/
theorem Prepared.increments_of_integrals {Ω : Type} {n d w j : Nat}
    {s : NamedSystem n d w j} (p : Prepared s) (ctx : Context Ω w j)
    (x : Process Ω (n + d)) (integrals : Channels w j → Process Ω n)
    (admitted : ctx.admissible) (axis : s.axis = ctx.time.axis)
    (regular : ∀ k, sampleAdmissible (s.kind k) ctx.time x)
    (checked : ∀ k i, ctx.integral (s.kind k)
      (fun t ω => (p.field k).run (sample (s.kind k) x t ω) i)
      (fun t ω => integrals k t ω i)) :
    s.Increments ctx x (fun t ω i => ∑ k, integrals k t ω i) := by
  refine ⟨p.valid, admitted, axis, (fun k t ω => (p.field k).run (sample (s.kind k) x t ω)),
    integrals, ?_, checked, rfl⟩
  intro k
  exact (p.evaluates_iff ctx.time k x _).mpr ⟨regular k, rfl⟩

/-- Observable initialized solutions are preserved; the compiler neither loses
nor creates a solution under the same context. Existence and uniqueness remain
separate analytic obligations. -/
theorem Prepared.solves_iff_circuit {Ω : Type} {n d w j : Nat}
    {s : NamedSystem n d w j} (p : Prepared s) (ctx : Context Ω w j)
    (u : Process Ω d) (initial : Ω → Point n) (x : Process Ω n) :
    s.Solves ctx u initial x ↔ p.compile.close.Rel ctx (append u (fun _ => initial)) x := by
  simp only [NamedSystem.Solves, Circuit.close_correct, p.increments_iff_circuit]

#print axioms Prepared.expression_correct
#print axioms Prepared.increments_iff_circuit
#print axioms Prepared.solves_iff_circuit
end Gimle.Asgard.Stochastic
