import Gimle.Asgard.Compile.Syntax
import Gimle.Asgard.Compile.Interchange

namespace Gimle.Asgard.Tests
open Polynomial

-- Empty contexts, exact fractions, shared inputs and asymmetric routing.
example (x : Point 0) : (Expr.constant (n := 0) (1 / 3)).compile.run x 0 = (1 / 3 : ℝ) := by
  rw [Expr.compile_correct]
  norm_num [Expr.eval]

example (x : Point 7) :
    (Expr.add (.var 5) (.var 5)).compile.run x 0 = x 5 + x 5 := by
  simp [Expr.compile_correct, Expr.eval]

example : (Expr.add (.var 2) (.neg (.var 0))).compile.run ![2, 5, 11] 0 = 9 := by
  rw [Expr.compile_correct]
  change (11 : ℝ) + -2 = 9
  norm_num

example (x : Point 0) : (compileOutputs (n := 0) (m := 0) Fin.elim0).run x = x := by
  funext i
  exact Fin.elim0 i

example (x : Point 9) : (route (fun i : Fin 3 => ![8, 2, 8] i)).run x = ![x 8, x 2, x 8] := by
  simp
  funext i
  fin_cases i <;> rfl

example (x : Point 3) :
    (route (fun i : Fin 3 => ![2, 0, 1] i)).run x = ![x 2, x 0, x 1] := by
  simp
  funext i
  fin_cases i <;> rfl

-- Concrete witnesses reject incorrect arithmetic and coordinate order.
example : Circuit.add.run ![2, 3] 0 ≠ (Expr.mul (.var 0) (.var 1)).eval ![2, 3] := by
  norm_num [Expr.eval]

example : (route (fun i : Fin 2 => i)).run ![2, 5] ≠ ![5, 2] := by
  intro h
  have bad := congrFun h 0
  norm_num at bad

def testInputs : List Port := [⟨"p-x", "x", .input⟩, ⟨"p-u", "u0", .driver⟩]

example : (inputBindings testInputs "u0") = some (.var ⟨1, by decide⟩) := by decide
example : (inputBindings testInputs "missing") = none := by decide
example : validPorts [⟨"p", "x", .input⟩, ⟨"p", "y", .input⟩] = false := by decide
example : validPorts [⟨"p", "x", .input⟩, ⟨"q", "x", .input⟩] = false := by decide

example : (Program.mk testInputs (equations% { z := x + u0; z := 1; })).resolve = none := by decide
example : (Program.mk testInputs (equations% { x := 1; })).resolve = none := by decide
example : (Program.mk testInputs (equations% { z := z + 1; })).resolve = none := by decide
example : (Program.mk testInputs (equations% { z := w; w := x; })).resolve = none := by decide
example : (Program.mk testInputs (equations% { z := missing; })).resolve = none := by decide
example : (Program.mk [⟨"x", "x", .output⟩] []).resolve = none := by decide

-- Binding and precedence are checked on the visible AST, separately from semantics.
example : (poly% x + 2 * u0) = NamedExpr.add (.var "x") (.mul (.constant 2) (.var "u0")) := rfl
example : (poly% -x ^ 2) = NamedExpr.neg ((NamedExpr.var "x").pow 2) := rfl
example : (poly% x - u0 - 1) = NamedExpr.add (.add (.var "x") (.neg (.var "u0"))) (.neg (.constant 1)) := rfl
example : (poly% rat(1, 3)) = NamedExpr.constant (1 / 3) := rfl

/-- error: Rational denominator must be positive -/
#guard_msgs in
#check poly% rat(1, 0)

open Interchange
example : decode (.compose .add .add) = none := by decide
#guard (RawCircuit.constant (1 / 3)).toPython ==
    .error "Python integer-coefficient interchange rejects non-integer rationals"
#guard (RawCircuit.constant (1 / 2)).toPython ==
    .error "Python integer-coefficient interchange rejects non-integer rationals"
example : (RawCircuit.constant (-123456789012345678901234567890)).toPython =
    .ok "const(-123456789012345678901234567890)" := by decide

example : (exportPython Circuit.id [] []).toOption = none := by decide
example : (exportPython Circuit.id [⟨"x", "x", .input⟩] [⟨"x", "y", .output⟩]).toOption = none := by decide

end Gimle.Asgard.Tests
