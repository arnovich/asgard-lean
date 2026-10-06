import Gimle.Asgard.Examples.EulerThreeMode
import Gimle.Asgard.Streams.MildTable

/-! Kernel-checked exact viscous interaction coefficients through degree two. -/
namespace Gimle.Asgard.Tests.MildTable

open Gimle.Asgard.Streams
open Gimle.Asgard.Examples

def startTable : Mild.Table := Mild.Table.embed EulerThreeMode.startTable
noncomputable def start : Mild.Stream := fun _ => Mild.embed EulerThreeMode.ω₀

theorem start_eq_table : startTable.toMild = start 0 := by
  rw [startTable, Mild.Table.toMild_embed, EulerThreeMode.start_eq_table]
  rfl

example (ν : ℚ) (n : ℕ) :
    Mild.wild ν start n = ((Mild.picard ν startTable n).get n).toMild :=
  Mild.stream_eq_table ν startTable start start_eq_table n

/-- The initial x mode has its exact heat exponential at rate one. -/
theorem heat_x : Mild.wild (1 / 10) start 0 (1, 0) =
    ExpPoly.Table.toExp [((1, 0), 1 / 2)] := by
  rw [Mild.stream_eq_table _ startTable start start_eq_table, Mild.Table.toMild_apply]
  exact congrArg ExpPoly.Table.toExp (by decide +kernel)

/-- The first interaction creates cos y with two cancelling exponentials. -/
theorem first_y : Mild.wild (1 / 10) start 1 (0, 1) =
    ExpPoly.Table.toExp [((1, 0), 5 / 8), ((3, 0), -5 / 8)] := by
  rw [Mild.stream_eq_table _ startTable start start_eq_table, Mild.Table.toMild_apply]
  exact congrArg ExpPoly.Table.toExp (by decide +kernel)

/-- Degree two includes both a resonant polynomial and nonresonant exponentials. -/
theorem second_2x2y : Mild.wild (1 / 10) start 2 (2, 2) = ExpPoly.Table.toExp
    [((8, 0), -35 / 13), ((14, 0), 5 / 26), ((8, 1), -5 / 13), ((6, 0), 5 / 2)] := by
  rw [Mild.stream_eq_table _ startTable start start_eq_table, Mild.Table.toMild_apply]
  exact congrArg ExpPoly.Table.toExp (by decide +kernel)

example : ((Mild.picard (1 / 10) startTable 0).get 0).length = 6 := by decide +kernel
example : ((Mild.picard (1 / 10) startTable 1).get 1).length = 12 := by decide +kernel
example : (((Mild.picard (1 / 10) startTable 1).get 1).map fun e => e.2.length).sum = 24 := by
  decide +kernel
example : ((Mild.picard (1 / 10) startTable 2).get 2).length = 28 := by decide +kernel
example : (((Mild.picard (1 / 10) startTable 2).get 2).map fun e => e.2.length).sum = 112 := by
  decide +kernel

#print axioms heat_x
#print axioms first_y
#print axioms second_2x2y

end Gimle.Asgard.Tests.MildTable
