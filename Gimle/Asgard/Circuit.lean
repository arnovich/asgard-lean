import Mathlib.Data.Rat.Defs

/-! Typed syntax for the real polynomial feedforward fragment. No interpretation
or property logic is imported here. Composition runs its left argument first. -/

namespace Gimle.Asgard

/-- Stable interpretation identifier; richer semantics require a separate version. -/
def fragmentVersion : String := "asgard.real-polynomial-feedforward/v1"

/-- Typed syntax for the supported deterministic feedforward circuit fragment.
Composition runs its left argument first, matching Asgard. -/
inductive Circuit : Nat → Nat → Type where
  | id : Circuit 1 1
  | const (value : ℚ) : Circuit 0 1
  | scalar (value : ℚ) : Circuit 1 1
  | add : Circuit 2 1
  | multiplication : Circuit 2 1
  | split : Circuit 1 2
  | swap : Circuit 2 2
  | terminal : Circuit 1 0
  | compose {input middle output : Nat} :
      Circuit input middle → Circuit middle output → Circuit input output
  | parallel {leftInput leftOutput rightInput rightOutput : Nat} :
      Circuit leftInput leftOutput → Circuit rightInput rightOutput →
      Circuit (leftInput + rightInput) (leftOutput + rightOutput)

end Gimle.Asgard
