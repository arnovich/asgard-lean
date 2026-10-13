import Gimle.Asgard.Streams.MildCircuit
import Gimle.Asgard.Streams.MildEvaluation

/-! The mild expansion is a unique interaction-degree stream of exact terms. -/
namespace Gimle.Asgard.Tests.Mild

open Gimle.Asgard.Streams
open Torus

example (ν : ℚ) (b : Mild.Stream) : Mild.wild ν b 0 = Mild.heat (b 0) :=
  Mild.wild_zero ν b

example (ν : ℚ) (b : Mild.Stream) (n : ℕ) :
    Mild.wild ν b (n + 1) = -Mild.duhamel ν
      (∑ m ∈ Finset.range (n + 1), Mild.transport (Mild.wild ν b m) (Mild.wild ν b (n - m))) :=
  Mild.wild_succ ν b n

example (ν : ℚ) (b : Mild.Stream) :
    (Mild.mildCircuit ν).Rel ![b] ![Mild.wild ν b] := Mild.mildCircuit_solution ν b

example (ν : ℚ) (b b' : Mild.Stream) (h : b 0 = b' 0) :
    Mild.wild ν b = Mild.wild ν b' := Mild.wild_congr_slice ν b b' h

example (b : TrigStream) (n : ℕ) (t : ℝ) :
    Mild.eval 0 t (Mild.wild 0 (fun m => Mild.embed (b m)) n) =
      t ^ n • Mild.realEmbed (NS.stream .ogf 0 b n) := Mild.wild_eval_zero b n t

/-- Boundary noise at positive interaction degrees cannot change the output. -/
example (ν : ℚ) (P Q : Mild.MildPoly) :
    Mild.wild ν (fun _ => P) = Mild.wild ν (fun n => if n = 0 then P else Q) := by
  apply Mild.wild_congr_slice
  simp

/-- Zero output is impossible for this nonzero physical initial mode. -/
example (ν : ℚ) : ¬(Mild.mildCircuit ν).Rel
    ![fun _ => Mild.embed (Finsupp.single (1, 0) 1)] ![0] := by
  intro h
  have h' := (Mild.mildCircuit_rel_iff ν _ _).mp h
  have hz := congrArg (fun output => Mild.eval ν 0 (output 0 0) (1, 0)) h'
  simp at hz

/-- info: 'Gimle.Asgard.Streams.Mild.mildCircuit_rel_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Mild.mildCircuit_rel_iff
/-- info: 'Gimle.Asgard.Streams.Mild.wild_eval_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Mild.wild_eval_zero

end Gimle.Asgard.Tests.Mild
