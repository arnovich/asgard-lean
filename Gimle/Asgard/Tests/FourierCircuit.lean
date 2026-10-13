import Gimle.Asgard.Streams.VorticityCircuit
import Gimle.Asgard.Examples.EulerThreeMode

/-! The Fourier circuit denotes the whole formal solution, in either basis.
The boundary is an input, not a supplied solution or a fixed example. -/
namespace Gimle.Asgard.Tests.FourierCircuit

open Streams Streams.Fourier Streams.NS

example (basis : Basis) (ν : ℚ) (boundary : TrigStream) :
    (vorticityCircuit basis ν).Rel ![boundary] ![stream basis ν boundary] :=
  vorticityCircuit_solution basis ν boundary

example (basis : Basis) (ν : ℚ) (boundary candidate : TrigStream) :
    (vorticityCircuit basis ν).Rel ![boundary] ![candidate] ↔
      TrigStream.derivative basis candidate = rhs basis ν candidate ∧
        candidate 0 = boundary 0 :=
  vorticityCircuit_rel_iff_pde basis ν boundary candidate

example (boundary : TrigStream) (y : Fourier.Point 1) :
    (vorticityCircuit .egf (1 / 10)).Rel ![boundary] y ↔
      y = ![stream .egf (1 / 10) boundary] :=
  vorticityCircuit_rel_iff _ _ _ _

example : ¬ (vorticityCircuit .ogf 0).Rel
    ![Examples.EulerThreeMode.start] ![0] := by
  intro h
  have initial := ((vorticityCircuit_rel_iff_pde _ _ _ _).mp h).2
  have mode := congrArg (fun p => p (1, 0)) initial
  norm_num [Examples.EulerThreeMode.start, Examples.EulerThreeMode.ω₀,
    Torus.cosine, Finsupp.single_apply] at mode

/-- A trace need not be deterministic: an identity feedback loop admits any stream. -/
example (a : TrigStream) :
    (Fourier.Circuit.trace 1 (Fourier.Circuit.route (basis := .ogf) ![1, 1])).Rel ![0] ![a] := by
  refine ⟨![a], ?_⟩
  change Fourier.append ![a] ![a] = Fourier.append ![0] ![a] ∘ ![1, 1]
  funext i
  fin_cases i <;> rfl

/--
info: 'Gimle.Asgard.Streams.NS.vorticityCircuit_rel_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms vorticityCircuit_rel_iff
/--
info: 'Gimle.Asgard.Streams.NS.vorticityCircuit_rel_iff_pde' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms vorticityCircuit_rel_iff_pde

end Gimle.Asgard.Tests.FourierCircuit
