import Gimle.Asgard.Streams.FourierCircuit
import Gimle.Asgard.Streams.Vorticity

/-! The vorticity equation as a Fourier circuit with an integrated feedback wire.
The sole external input is the boundary stream. The solution is an output,
never an input assumption. Both OGF and EGF, and any rational viscosity, are
covered formally; analytic realization is a separate property.
-/
namespace Gimle.Asgard.Streams.NS

open Fourier

/-- Input 0 is the boundary; input 1 is the feedback vorticity. -/
def rhsExpr (ν : ℚ) : Expr 2 :=
  .add (.scale ν (.laplacian (.input 1)))
    (.scale (-1) (.transport (.input 1) (.input 1)))

/-- Integrate the compiled right-hand side, preserving the external initial slice. -/
def rebuiltExpr (ν : ℚ) : Expr 2 := .integralFrom (rhsExpr ν) (.input 0)

/-- Expose the feedback state and return its reconstruction to the loop. -/
def vorticityBody (basis : Basis) (ν : ℚ) : Fourier.Circuit basis 2 2 :=
  .pair ((Expr.input 1).compile basis) ((rebuiltExpr ν).compile basis)

/-- A single integrated feedback loop, from boundary data to the solution stream. -/
def vorticityCircuit (basis : Basis) (ν : ℚ) : Fourier.Circuit basis 1 1 :=
  .trace 1 (vorticityBody basis ν)

/-- The syntactic right-hand side denotes the previously defined Fourier equation. -/
theorem rhsExpr_value (basis : Basis) (ν : ℚ) (boundary state : TrigStream) :
    (rhsExpr ν).value basis ![boundary, state] = rhs basis ν state := by
  funext degree
  simp [rhsExpr, Expr.value, rhs, sub_eq_add_neg]

/-- The loop relation is precisely reconstruction by integration. -/
theorem vorticityCircuit_rel_iff_reconstructs (basis : Basis) (ν : ℚ)
    (boundary candidate : TrigStream) :
    (vorticityCircuit basis ν).Rel ![boundary] ![candidate] ↔
      TrigStream.integral basis (rhs basis ν candidate) boundary = candidate := by
  simp only [vorticityCircuit, Fourier.Circuit.Rel, vorticityBody, Expr.compile_rel]
  constructor
  · rintro ⟨feedback, a, b, ha, hb, h⟩
    change a = ![feedback 0] at ha
    subst a
    subst b
    have output : candidate = feedback 0 := congrArg (fun p => p 0) h
    have loop : feedback 0 = (rebuiltExpr ν).value basis
        (Fourier.append ![boundary] feedback) := congrArg (fun p => p 1) h
    have input_eq : Fourier.append ![boundary] feedback = ![boundary, candidate] := by
      funext i
      fin_cases i
      · rfl
      · exact output.symm
    rw [input_eq] at loop
    change feedback 0 = TrigStream.integral basis
      ((rhsExpr ν).value basis ![boundary, candidate]) boundary at loop
    rw [rhsExpr_value, ← output] at loop
    exact loop.symm
  · intro h
    refine ⟨![candidate], ![candidate], ![candidate], rfl, ?_, rfl⟩
    change ![candidate] = ![TrigStream.integral basis ((rhsExpr ν).value basis ![boundary, candidate]) boundary]
    rw [rhsExpr_value, h]

/-- The actual circuit relation is equivalent to the PDE recurrence and initial slice. -/
theorem vorticityCircuit_rel_iff_pde (basis : Basis) (ν : ℚ)
    (boundary candidate : TrigStream) :
    (vorticityCircuit basis ν).Rel ![boundary] ![candidate] ↔
      TrigStream.derivative basis candidate = rhs basis ν candidate ∧
        candidate 0 = boundary 0 := by
  rw [vorticityCircuit_rel_iff_reconstructs, reconstructs_iff]

/-- Every related output is the constructed stream; the trace is not merely assumed safe. -/
theorem vorticityCircuit_rel_iff (basis : Basis) (ν : ℚ)
    (boundary : TrigStream) (output : Fourier.Point 1) :
    (vorticityCircuit basis ν).Rel ![boundary] output ↔ output = ![stream basis ν boundary] := by
  have eta : output = ![output 0] := by ext i; fin_cases i; rfl
  rw [eta, vorticityCircuit_rel_iff_pde]
  constructor
  · rintro ⟨pde, initial⟩
    rw [eq_stream basis ν boundary (output 0) pde initial]
  · intro h
    have value := congrArg (fun p => p 0) h
    simp only [Matrix.cons_val_zero] at value
    rw [value]
    exact ⟨stream_pde basis ν boundary, stream_slice basis ν boundary⟩

/-- Every boundary has a related solution. -/
theorem vorticityCircuit_solution (basis : Basis) (ν : ℚ) (boundary : TrigStream) :
    (vorticityCircuit basis ν).Rel ![boundary] ![stream basis ν boundary] :=
  (vorticityCircuit_rel_iff basis ν boundary _).mpr rfl

end Gimle.Asgard.Streams.NS
