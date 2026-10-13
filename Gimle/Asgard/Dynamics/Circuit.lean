import Gimle.Asgard.Compile.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Continuous trajectory circuits have relational semantics, separate from the
feedforward real-function interpretation. A trace asserts no fixed-point theorem. -/
namespace Gimle.Asgard.Dynamics

def fragmentVersion : String := "asgard.real-continuous-feedback/v1"

abbrev Signal (n : Nat) := ℝ → Point n

def signalAppend {n m : Nat} (x : Signal n) (y : Signal m) : Signal (n + m) :=
  fun t => pointAppend (x t) (y t)

def signalLeft {n m : Nat} (x : Signal (n + m)) : Signal n := fun t => pointLeft (x t)
def signalRight {n m : Nat} (x : Signal (n + m)) : Signal m := fun t => pointRight (x t)

@[simp] theorem signalLeft_append {n m : Nat} (x : Signal n) (y : Signal m) :
    signalLeft (signalAppend x y) = x := by funext t; simp [signalLeft, signalAppend]

@[simp] theorem signalRight_append {n m : Nat} (x : Signal n) (y : Signal m) :
    signalRight (signalAppend x y) = y := by funext t; simp [signalRight, signalAppend]

@[simp] theorem signalAppend_parts {n m : Nat} (x : Signal (n + m)) :
    signalAppend (signalLeft x) (signalRight x) = x := by
  funext t i
  simp only [signalAppend, signalLeft, signalRight, pointAppend, pointLeft, pointRight]
  split
  · rfl
  · congr 1
    apply Fin.ext
    simp_all
    omega

/-- The supported domain is the forward half-line, including its initial point.
The axis ID is distinct from state names. Other horizons are a later extension. -/
structure TimeDomain where
  axis : String
  start : ℝ

def TimeDomain.domain (time : TimeDomain) : Set ℝ := Set.Ici time.start

/-- Explicit typed continuous syntax. `integrate axis n` is a bank of n scalar
integrators: inputs are [derivatives, initial values], outputs are states. -/
inductive Circuit : Nat → Nat → Type where
  | lift {n m : Nat} : Gimle.Asgard.Circuit n m → Circuit n m
  | integrate (axis : String) (n : Nat) : Circuit (n + n) n
  | compose {n k m : Nat} : Circuit n k → Circuit k m → Circuit n m
  | parallel {n m k l : Nat} : Circuit n m → Circuit k l → Circuit (n + k) (m + l)
  | trace {n m : Nat} (k : Nat) : Circuit (n + k) (m + k) → Circuit n m

/-- Wire equations hold for the supplied full signals. Derivatives are required
within the forward time domain only. An initial wire is read once at `start`;
its values at other times are ignored. No numerical integration is involved. -/
def Circuit.Rel {n m : Nat} : Circuit n m → TimeDomain → Signal n → Signal m → Prop
  | .lift c, _, x, y => y = fun t => c.run (x t)
  | .integrate axis n, time, x, y =>
      axis = time.axis ∧ y time.start = pointRight (x time.start) ∧
        ∀ t ∈ time.domain, ∀ i : Fin n,
          HasDerivWithinAt (fun t => y t i) (pointLeft (x t) i) time.domain t
  | .compose a b, time, x, y => ∃ z, a.Rel time x z ∧ b.Rel time z y
  | .parallel a b, time, x, y =>
      a.Rel time (signalLeft x) (signalLeft y) ∧
        b.Rel time (signalRight x) (signalRight y)
  | .trace _ body, time, x, y =>
      ∃ feedback, body.Rel time (signalAppend x feedback) (signalAppend y feedback)

/-- Relational rewrites preserve all externally supplied signals, including
initial-condition wires; no total evaluator or well-posedness is assumed. -/
def Equivalent {n m : Nat} (a b : Circuit n m) : Prop :=
  ∀ time x y, a.Rel time x y ↔ b.Rel time x y

end Gimle.Asgard.Dynamics
