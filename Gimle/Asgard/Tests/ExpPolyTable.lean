import Gimle.Asgard.Streams.ExpPolyTable

/-! Kernel computations cover every resonance branch, including negative c. -/
namespace Gimle.Asgard.Tests.ExpPolyTable

open Gimle.Asgard.Streams

example : ExpPoly.Table.coeff 2 1 (ExpPoly.Table.duhamel 0 1 [((2, 0), 1)]) = 1 := by
  decide +kernel

example : ExpPoly.Table.coeff 2 1 (ExpPoly.Table.duhamel 1 2 [((2, 0), 1)]) = 1 := by
  decide +kernel

example : ExpPoly.Table.coeff 2 0 (ExpPoly.Table.duhamel 1 1 [((2, 0), 1)]) = -1 := by
  decide +kernel

example : ExpPoly.Table.coeff 1 0 (ExpPoly.Table.duhamel 1 1 [((2, 0), 1)]) = 1 := by
  decide +kernel

example (ν : ℚ) (μ : ℕ) (l : ExpPoly.Table) :
    (ExpPoly.Table.duhamel ν μ l).toExp = ExpPoly.duhamel ν μ l.toExp :=
  ExpPoly.Table.toExp_duhamel ν μ l

end Gimle.Asgard.Tests.ExpPolyTable
