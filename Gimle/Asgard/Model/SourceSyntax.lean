import Gimle.Asgard.Model.Source
import Lean

/-! Source notation for `Model.Term`, shaped like the Python source grammar, and
for the explicit assignments, differential equations and velocity declarations
of a `SourceBody`.

`diff(x, t)` is a derivative atom, `int(x, t)` the integral over `t` from the
declared start, `(λ w => body)(arg)` an applied lambda,
`e / n` division by a positive numeral and `e ^ n` a positive numeral power,
expanded to repeated multiplication. `^ 0` is refused so that no written term,
derivative or reference, can disappear before it is checked. Unary `+` is the
identity. The guarantees start at the resulting
`Term` AST; this macro is tested, not a verified parser. -/
namespace Gimle.Asgard.Model

def Term.pow (e : Term) : Nat → Term
  | 0 => .constant 1
  | n + 1 => .mul (e.pow n) e

declare_syntax_cat asgardTerm
syntax ident : asgardTerm
syntax num : asgardTerm
syntax "(" asgardTerm ")" : asgardTerm
syntax "rat(" num "," num ")" : asgardTerm
syntax "diff(" asgardTerm "," ident ")" : asgardTerm
syntax "int(" asgardTerm "," ident ")" : asgardTerm
syntax "(" "λ " ident " => " asgardTerm ")" "(" asgardTerm ")" : asgardTerm
syntax:65 asgardTerm:65 " + " asgardTerm:66 : asgardTerm
syntax:65 asgardTerm:65 " - " asgardTerm:66 : asgardTerm
syntax:70 asgardTerm:70 " * " asgardTerm:71 : asgardTerm
syntax:70 asgardTerm:70 " / " num : asgardTerm
syntax:75 "-" asgardTerm:75 : asgardTerm
syntax:75 "+" asgardTerm:75 : asgardTerm
syntax:80 asgardTerm:81 " ^ " num : asgardTerm
syntax "term% " asgardTerm : term

macro_rules
  | `(term% $x:ident) => `(Term.var $(Lean.quote x.getId.toString))
  | `(term% $n:num) => `(Term.constant $n)
  | `(term% ($e:asgardTerm)) => `(term% $e)
  | `(term% rat($a:num, $b:num)) => do
      if b.getNat == 0 then Lean.Macro.throwErrorAt b "Rational denominator must be positive"
      `(Term.constant (($a : ℚ) / $b))
  | `(term% diff($e:asgardTerm, $axis:ident)) =>
      `(Term.derivative $(Lean.quote axis.getId.toString) (term% $e))
  | `(term% int($e:asgardTerm, $axis:ident)) =>
      `(Term.integral $(Lean.quote axis.getId.toString) (term% $e))
  | `(term% (λ $x:ident => $body:asgardTerm)($arg:asgardTerm)) =>
      `(Term.apply $(Lean.quote x.getId.toString) (term% $body) (term% $arg))
  | `(term% $a:asgardTerm + $b:asgardTerm) => `(Term.add (term% $a) (term% $b))
  | `(term% $a:asgardTerm - $b:asgardTerm) => `(Term.add (term% $a) (.neg (term% $b)))
  | `(term% $a:asgardTerm * $b:asgardTerm) => `(Term.mul (term% $a) (term% $b))
  | `(term% $a:asgardTerm / $n:num) => do
      if n.getNat == 0 then Lean.Macro.throwErrorAt n "Division is by a positive numeral"
      `(Term.mul (term% $a) (.constant ((1 : ℚ) / $n)))
  | `(term% -$a:asgardTerm) => `(Term.neg (term% $a))
  | `(term% +$a:asgardTerm) => `(term% $a)
  | `(term% $a:asgardTerm ^ $n:num) => do
      if n.getNat == 0 then Lean.Macro.throwErrorAt n "Exponent must be a positive numeral"
      `(Term.pow (term% $a) $n)

/-- Explicit assignments, each with an output port whose ID and name are the
written identifier. -/
syntax "assignments%" "{" (ident " := " asgardTerm ";")* "}" : term
macro_rules
  | `(assignments% { $[$names:ident := $bodies:asgardTerm;]* }) => do
      let terms ← names.zip bodies |>.mapM fun (name, body) => do
        let label := Lean.quote name.getId.toString
        `(SourceAssignment.mk (Polynomial.Port.mk $label $label .output) (term% $body))
      `([$terms,*])

/-- Differential equations `port : lhs = rhs`, where `port` is the derivative
port that a `StateBinding` names. -/
syntax "differentials%" "{" (ident " : " asgardTerm " = " asgardTerm ";")* "}" : term
macro_rules
  | `(differentials% { $[$names:ident : $lhss:asgardTerm = $rhss:asgardTerm;]* }) => do
      let terms ← (names.zip (lhss.zip rhss)).mapM fun (name, lhs, rhs) => do
        let label := Lean.quote name.getId.toString
        `(DifferentialEquation.mk (Polynomial.Port.mk $label $label .output)
          (term% $lhs) (term% $rhs))
      `([$terms,*])

/-- Velocity declarations `port : diff(state, axis) = velocity`, where `port` is
the derivative port of `state` and `velocity` a declared state. -/
syntax "velocities%" "{" (ident " : " "diff(" ident "," ident ")" " = " ident ";")* "}" : term
macro_rules
  | `(velocities% { $[$names:ident : diff($states:ident, $axes:ident) = $velocities:ident;]* }) => do
      let terms ← (names.zip (states.zip (axes.zip velocities))).mapM
        fun (name, state, axis, velocity) => do
          let label := Lean.quote name.getId.toString
          `(VelocityDeclaration.mk (Polynomial.Port.mk $label $label .output)
            $(Lean.quote axis.getId.toString) $(Lean.quote state.getId.toString)
            $(Lean.quote velocity.getId.toString))
      `([$terms,*])

end Gimle.Asgard.Model
