import Gimle.Asgard.Tests.MildTable

/-! Degree-three kernel cost is measured separately from the smaller regressions. -/
namespace Gimle.Asgard.Tests.MildDegreeThree

open Gimle.Asgard.Streams
open MildTable (start startTable start_eq_table)

/-- A coefficient involving cancellation among ten distinct heat rates. -/
theorem third_x_rate_one :
    (((Mild.wild (1 / 10) start 3 (1, 0)).coeff 1).coeff 0) = -5247629 / 15375360 := by
  rw [Mild.stream_coeff _ startTable start start_eq_table]
  decide +kernel

example : ((Mild.picard (1 / 10) startTable 3).get 3).length = 52 := by decide +kernel
example : (((Mild.picard (1 / 10) startTable 3).get 3).map fun e => e.2.length).sum = 382 := by
  decide +kernel

#print axioms third_x_rate_one

end Gimle.Asgard.Tests.MildDegreeThree
