import Gimle.Asgard.Compile.Named
import Lean

/-! Small, inspectable source notation. The preservation theorem starts at the
resulting NamedExpr/Program AST. This macro implementation is tested, not a
formally verified parser for text. -/
namespace Gimle.Asgard.Polynomial

def NamedExpr.pow (e : NamedExpr) : Nat → NamedExpr
  | 0 => .constant 1
  | n + 1 => .mul (e.pow n) e

declare_syntax_cat asgardPoly
syntax ident : asgardPoly
syntax num : asgardPoly
syntax "(" asgardPoly ")" : asgardPoly
syntax "rat(" num "," num ")" : asgardPoly
syntax:65 asgardPoly:65 " + " asgardPoly:66 : asgardPoly
syntax:65 asgardPoly:65 " - " asgardPoly:66 : asgardPoly
syntax:70 asgardPoly:70 " * " asgardPoly:71 : asgardPoly
syntax:75 "-" asgardPoly:75 : asgardPoly
syntax:80 asgardPoly:81 " ^ " num : asgardPoly
syntax "poly% " asgardPoly : term

macro_rules
  | `(poly% $x:ident) => `(NamedExpr.var $(Lean.quote x.getId.toString))
  | `(poly% $n:num) => `(NamedExpr.constant $n)
  | `(poly% ($e:asgardPoly)) => `(poly% $e)
  | `(poly% rat($a:num, $b:num)) => do
      if b.getNat == 0 then Lean.Macro.throwErrorAt b "Rational denominator must be positive"
      `(NamedExpr.constant (($a : ℚ) / $b))
  | `(poly% $a:asgardPoly + $b:asgardPoly) => `(NamedExpr.add (poly% $a) (poly% $b))
  | `(poly% $a:asgardPoly - $b:asgardPoly) => `(NamedExpr.add (poly% $a) (.neg (poly% $b)))
  | `(poly% $a:asgardPoly * $b:asgardPoly) => `(NamedExpr.mul (poly% $a) (poly% $b))
  | `(poly% -$a:asgardPoly) => `(NamedExpr.neg (poly% $a))
  | `(poly% $a:asgardPoly ^ $n:num) => `(NamedExpr.pow (poly% $a) $n)

syntax "equations%" "{" (ident " := " asgardPoly ";")* "}" : term
macro_rules
  | `(equations% { $[$names:ident := $bodies:asgardPoly;]* }) => do
      let terms ← names.zip bodies |>.mapM fun (name, body) => do
        let label := Lean.quote name.getId.toString
        `(Assignment.mk (Port.mk $label $label .output) (poly% $body))
      `([$terms,*])

end Gimle.Asgard.Polynomial
