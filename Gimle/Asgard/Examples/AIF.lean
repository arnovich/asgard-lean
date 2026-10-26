module

public import Gimle.Asgard.Compile.Syntax
public import Gimle.Asgard.Dynamics.Feedback

/-! Four-species antithetic integral feedback (AIF), compiled to typed circuits.
Eta is a real input fixed along each feedback trajectory. These equivalences
assert no trajectory existence, uniqueness, species positivity or safety bound. -/

@[expose] public section

namespace Gimle.Asgard.Examples.AIF
open _root_.Gimle.Asgard.Polynomial

def inputs : List Port := [⟨"eta", "eta", .driver⟩,
  ⟨"x1", "x1", .state⟩, ⟨"x2", "x2", .state⟩,
  ⟨"z1", "z1", .state⟩, ⟨"z2", "z2", .state⟩]

/-- Plant gain one and reference two, with physical species in order x1,x2,z1,z2. -/
def source : Program := {
  inputs := inputs
  assignments := equations% {
    dx1 := z1 - x1;
    dx2 := x1 - x2;
    dz1 := 2 - eta * z1 * z2;
    dz2 := x2 - eta * z1 * z2;
  }
}

def expressions : List (Expr 5) := source.resolve.get (by decide +kernel)
def field : Circuit 5 4 := compileList expressions

theorem resolved : source.resolve = some expressions := (Option.some_get _).symm

/-- The original named equations and the compiled field have exactly the same values. -/
theorem source_satisfaction (x : Point 5) (values : List ℝ) :
    source.Satisfies x values ↔ List.ofFn (field.run x) = values :=
  source.satisfies_iff_compiled expressions resolved x values

/-- The input order is eta followed by the four physical species. -/
theorem field_equations (x : Point 5) : field.run x =
    ![x 3 - x 1, x 1 - x 2, 2 - x 0*x 3*x 4, x 2 - x 0*x 3*x 4] := by
  rw [show field = compileOutputs (fun i => expressions[i]) from rfl,
    compileOutputs_correct]
  have ast : expressions =
      [.add (.var 3) (.neg (.var 1)), .add (.var 1) (.neg (.var 2)),
       .add (.constant 2) (.neg (.mul (.mul (.var 0) (.var 3)) (.var 4))),
       .add (.var 2) (.neg (.mul (.mul (.var 0) (.var 3)) (.var 4)))] := by
    decide +kernel
  ext i
  fin_cases i <;> simp [ast, Expr.eval, sub_eq_add_neg,
    Matrix.cons_val_two, Matrix.cons_val_three]

theorem field_appended (eta : ℝ) (x : Point 4) :
    field.run (pointAppend ![eta] x) =
      ![x 2 - x 0, x 0 - x 1, 2 - eta*x 2*x 3, x 1 - eta*x 2*x 3] := by
  rw [field_equations]
  rfl

/-- Feed the state outputs back into the same source-compiled field. -/
def feedback : Dynamics.Circuit 5 4 := Dynamics.close (d := 1) (n := 4) "t" field
noncomputable def time : Dynamics.TimeDomain := ⟨"t", 0⟩
noncomputable def drivers (eta : ℝ) : Dynamics.Signal 1 := fun _ => ![eta]

def Realizes (eta : ℝ) (state : Dynamics.Signal 4) : Prop :=
  feedback.Rel time (Dynamics.signalAppend (drivers eta) (fun _ => (0 : Point 4))) state

/-- Fixed real eta and zero initialization are part of the original feedback relation. -/
theorem realizes_iff (eta : ℝ) (state : Dynamics.Signal 4) :
    Realizes eta state ↔ state 0 = 0 ∧
      ∀ t ∈ Set.Ici (0 : ℝ), ∀ i,
        HasDerivWithinAt (fun s => state s i)
          (![state t 2 - state t 0, state t 0 - state t 1,
            2 - eta*state t 2*state t 3,
            state t 1 - eta*state t 2*state t 3] i) (Set.Ici 0) t := by
  rw [Realizes, feedback, Dynamics.close_correct]
  simp only [time, Dynamics.TimeDomain.domain, drivers, field_appended, true_and]

/-- The observation reads the plant's second species from the physical state. -/
def output : Circuit 4 1 := route (fun _ => 1)

theorem output_correct (x : Point 4) : output.run x 0 = x 1 := by
  simp [output]

#print axioms resolved
#print axioms source_satisfaction
#print axioms field_equations
#print axioms field_appended
#print axioms realizes_iff
#print axioms output_correct
end Gimle.Asgard.Examples.AIF
