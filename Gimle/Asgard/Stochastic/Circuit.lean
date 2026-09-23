import Gimle.Asgard.Compile.Polynomial
import Mathlib.Topology.Order.LeftRightLim

/-! Conditional physical-time process circuits. Integral relations are explicit
parameters, not axioms implementing stochastic calculus. No Brownian law,
existence theorem, probability bound or numerical accuracy follows from this API. -/
namespace Gimle.Asgard.Stochastic
open scoped BigOperators Topology

def fragmentVersion : String := "asgard.polynomial-process-translation/v1"

abbrev Process (Ω : Type) (n : Nat) := ℝ → Ω → Point n
abbrev ScalarProcess (Ω : Type) := ℝ → Ω → ℝ

def append {Ω : Type} {n m : Nat} (x : Process Ω n) (y : Process Ω m) :
    Process Ω (n + m) := fun t ω => pointAppend (x t ω) (y t ω)

def left {Ω : Type} {n m : Nat} (x : Process Ω (n + m)) : Process Ω n :=
  fun t ω => pointLeft (x t ω)
def right {Ω : Type} {n m : Nat} (x : Process Ω (n + m)) : Process Ω m :=
  fun t ω => pointRight (x t ω)

@[simp] theorem left_append {Ω : Type} {n m : Nat} (x : Process Ω n) (y : Process Ω m) :
    left (append x y) = x := by funext t ω; simp [left, append]
@[simp] theorem right_append {Ω : Type} {n m : Nat} (x : Process Ω n) (y : Process Ω m) :
    right (append x y) = y := by funext t ω; simp [right, append]

/-- Values immediately before a jump. Analytic realizations must ensure the
required left limits exist; `Function.leftLim` alone supplies no regularity. -/
noncomputable def before {Ω : Type} {n : Nat} (x : Process Ω n) : Process Ω n :=
  fun t ω i => Function.leftLim (fun s => x s ω i) t

structure Window where
  axis : String
  start : ℝ
  stop : ℝ
  ordered : start ≤ stop

def Window.domain (time : Window) : Set ℝ := Set.Icc time.start time.stop

/-- Left-limit sampling is admitted only where the required limits exist. -/
def HasLeftLimits {Ω : Type} {n : Nat} (time : Window) (x : Process Ω n) : Prop :=
  ∀ t ∈ time.domain, ∀ ω i, ∃ v,
    Filter.Tendsto (fun r => x r ω i) (𝓝[<] t) (𝓝 v)

inductive Calculus where
  | ito | stratonovich
  deriving Repr, DecidableEq, BEq

inductive JumpConvention where
  | uncompensated | compensated
  deriving Repr, DecidableEq, BEq

/-- Separate relation fields make calculus changes observable. Arguments are
window, actual driving process, integrand, and proposed integral process.
A realized stochastic interpretation must supply its probability space,
filtration, adaptedness/integrability and law premises through `Context.admissible`
and these relations. There is no default Brownian interpretation. -/
structure IntegralSemantics (Ω : Type) where
  time : Window → ScalarProcess Ω → ScalarProcess Ω → Prop
  ito : Window → ScalarProcess Ω → ScalarProcess Ω → ScalarProcess Ω → Prop
  stratonovich : Window → ScalarProcess Ω → ScalarProcess Ω → ScalarProcess Ω → Prop
  uncompensated : Window → ScalarProcess Ω → ScalarProcess Ω → ScalarProcess Ω → Prop
  compensated : Window → ScalarProcess Ω → ScalarProcess Ω → ScalarProcess Ω → Prop

/-- All coordinates share one sample space and joint driver assignment. Separate
coordinates do not imply independence. No covariance/law string overrides them. -/
structure Context (Ω : Type) (w j : Nat) where
  time : Window
  integrals : IntegralSemantics Ω
  noise : Fin w → ScalarProcess Ω
  jumps : Fin j → ScalarProcess Ω
  admissible : Prop

inductive IntegralKind (w j : Nat) where
  | time
  | noise (calculus : Calculus) (driver : Fin w)
  | jump (convention : JumpConvention) (driver : Fin j)

/-- Dispatch uses the actual driver at the declared coordinate. -/
def Context.integral {Ω : Type} {w j : Nat} (ctx : Context Ω w j) :
    IntegralKind w j → ScalarProcess Ω → ScalarProcess Ω → Prop
  | .time => ctx.integrals.time ctx.time
  | .noise .ito k => ctx.integrals.ito ctx.time (ctx.noise k)
  | .noise .stratonovich k => ctx.integrals.stratonovich ctx.time (ctx.noise k)
  | .jump .uncompensated k => ctx.integrals.uncompensated ctx.time (ctx.jumps k)
  | .jump .compensated k => ctx.integrals.compensated ctx.time (ctx.jumps k)

/-- Process syntax is separate from finite-vector real circuit syntax. `sum`
shares the complete input with every branch. `feedback` explicitly initializes
and closes the state inputs; compilation itself returns a pre-trace circuit. -/
inductive Circuit (w j : Nat) : Nat → Nat → Type where
  | lift {n m : Nat} : Gimle.Asgard.Circuit n m → Circuit w j n m
  | before (n : Nat) : Circuit w j n n
  | integrate (kind : IntegralKind w j) (n : Nat) : Circuit w j n n
  | compose {n k m : Nat} : Circuit w j n k → Circuit w j k m → Circuit w j n m
  | sum {n m : Nat} (k : Nat) : (Fin k → Circuit w j n m) → Circuit w j n m
  | guard {n m : Nat} (axis : String) : Circuit w j n m → Circuit w j n m
  | feedback {n d : Nat} : Circuit w j (n + d) n → Circuit w j (d + n) n

/-- Full wire processes are shared. Initialization/evolution is constrained on
the declared closed window only; paths outside it are not fixed by feedback. -/
def Circuit.Rel {Ω : Type} {w j n m : Nat} :
    Circuit w j n m → Context Ω w j → Process Ω n → Process Ω m → Prop
  | .lift c, _, x, y => y = fun t ω => c.run (x t ω)
  | .before _, ctx, x, y => HasLeftLimits ctx.time x ∧ y = Stochastic.before x
  | .integrate kind _, ctx, x, y => ∀ i,
      ctx.integral kind (fun t ω => x t ω i) (fun t ω => y t ω i)
  | .compose a b, ctx, x, y => ∃ z, a.Rel ctx x z ∧ b.Rel ctx z y
  | .sum k branches, ctx, x, y => ∃ values : Fin k → Process Ω _,
      (∀ i, (branches i).Rel ctx x (values i)) ∧ y = fun t ω i => ∑ k, values k t ω i
  | .guard axis c, ctx, x, y => ctx.admissible ∧ axis = ctx.time.axis ∧ c.Rel ctx x y
  | .feedback c, ctx, x, y => ∃ state increments,
      c.Rel ctx (append state (left x)) increments ∧ state = y ∧
      (∀ ω, y ctx.time.start ω = right x ctx.time.start ω) ∧
      ∀ t ∈ ctx.time.domain, ∀ ω i,
        y t ω i = right x ctx.time.start ω i + increments t ω i

/-- Physical-time closure is an explicit operation, never inserted by the
coefficient compiler or confused with coefficient-space feedback. -/
def Circuit.close {w j n d : Nat} (c : Circuit w j (n + d) n) :
    Circuit w j (d + n) n := .feedback c

theorem Circuit.close_correct {Ω : Type} {w j n d : Nat}
    (c : Circuit w j (n + d) n) (ctx : Context Ω w j) (u : Process Ω d)
    (initial : Ω → Point n) (x : Process Ω n) :
    c.close.Rel ctx (append u (fun _ => initial)) x ↔
      ∃ increments, c.Rel ctx (append x u) increments ∧
        (∀ ω, x ctx.time.start ω = initial ω) ∧
        ∀ t ∈ ctx.time.domain, ∀ ω i, x t ω i = initial ω i + increments t ω i := by
  simp only [close, Rel, left_append, right_append]
  constructor
  · rintro ⟨state, increments, h, rfl, hi, he⟩
    exact ⟨increments, h, hi, he⟩
  · rintro ⟨increments, h, hi, he⟩
    exact ⟨x, increments, h, rfl, hi, he⟩

#print axioms Circuit.close_correct
end Gimle.Asgard.Stochastic
