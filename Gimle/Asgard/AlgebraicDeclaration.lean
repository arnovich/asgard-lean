import Gimle.Asgard.AlgebraicCompiler
import Gimle.Asgard.Model.Declaration

/-! # Declared affine algebraic loops

An algebraic declaration names

* its **ports**, in coordinate order [loop, external]: the loop unknowns are
  `.state` ports read at coordinates `0 … n-1` of every loop and output circuit,
  the external inputs `.input` or `.parameter` ports read at `n … n+d-1`, and the
  observed outputs `.output` ports (`Declaration.coordinates`);
* its **equations**, as an exact rational `Problem`: simultaneous affine loop
  equations `z = M z + b(u)` and affine outputs `y = C (z ++ u) + c`;
* a **supplied inverse** of `1 - M`, unchecked until compilation;
* the **loop domain** and the **admitted inputs**, arbitrary predicates;
* the **membership obligation** `∀ u, admitted u → domain (solution u)`, where
  `solution` multiplies by the supplied inverse. It is a proof carried by the
  declaration value, not a validator check: a declaration whose obligation is
  false cannot be written down at all.

`Declaration.validate` checks the ports (IDs, names, roles) and both products of
the supplied inverse; a wrong inverse, and so every inverse of a singular loop,
is refused with `invalidInverse`, never solved. `Declaration.compile` returns an
`AlgebraicModel` carrying the checked `Inverse`.

Two theorems are kept apart:

* `Declaration.solves_iff_rel`: for **every** input, and for every declaration,
  accepted or not, the source equations hold exactly when the compiled loop and
  output circuits are related by `Rel` (`compile_correct`). It asserts neither
  existence nor uniqueness.
* `AlgebraicModel.eliminate_correct`: for an accepted declaration and an
  **admitted** input, there is exactly one loop point in the domain, and `Rel`
  holds exactly of the eliminated circuit's output (`Problem.eliminate_correct`).
  Nothing is said about inputs outside `admitted`.

This is a type of its own rather than a case of `Model.Declaration`: that type is
plain data (`Repr`, `DecidableEq`) whose `Body` is a polynomial `Program` the
common compiler schedules, rejecting every cycle as `cyclicDependency`, while
this declaration carries predicates and a proof obligation. Only affine loops
are declared; nonlinear elimination is out of scope. -/
namespace Gimle.Asgard.Algebraic
open Polynomial Matrix

/-- Simultaneous affine loop equations with ports in the order [loop, external],
a supplied inverse of `1 - M`, a loop domain, admitted inputs, and the proof
that every admitted input's eliminated solution lies in the domain. -/
structure Declaration (n d o : Nat) where
  loop : Fin n → Port
  external : Fin d → Port
  outputs : Fin o → Port
  problem : Problem n d o
  inverse : RationalMatrix n n
  domain : Point n → Prop
  admitted : Point d → Prop
  membership : ∀ u, admitted u → domain ((problem.solutionCircuit inverse).run u)

/-- The ports read by the loop and output circuits, in coordinate order. -/
def Declaration.coordinates {n d o : Nat} (a : Declaration n d o) : Fin (n + d) → Port :=
  Fin.addCases a.loop a.external

/-- **Coordinate order [loop, external].** The first `n` coordinates are the
loop ports and carry the loop point; the next `d` are the external ports and
carry the input. -/
theorem Declaration.coordinates_loop {n d o : Nat} (a : Declaration n d o) (i : Fin n)
    (z : Point n) (u : Point d) :
    a.coordinates (Fin.castAdd d i) = a.loop i ∧ pointAppend z u (Fin.castAdd d i) = z i := by
  simp [coordinates]

theorem Declaration.coordinates_external {n d o : Nat} (a : Declaration n d o) (j : Fin d)
    (z : Point n) (u : Point d) :
    a.coordinates (Fin.natAdd n j) = a.external j ∧ pointAppend z u (Fin.natAdd n j) = u j := by
  simp [coordinates]

private def require (condition : Bool) (code : Model.ErrorCode) (site reference : String) :
    Except Model.Diagnostic Unit :=
  if condition then .ok () else .error ⟨code, site, reference⟩

private def checkUnique (values : List String) (code : Model.ErrorCode) (site : String) :
    Except Model.Diagnostic Unit := do
  let mut seen := []
  for value in values do
    require (!seen.contains value) code site value
    seen := value :: seen

/-- Both products of a supplied inverse of `1 - m`, left first. -/
def checkInverse {n : Nat} (m value : RationalMatrix n n) :
    Except Model.Diagnostic (Inverse m) :=
  if left : value * (1 - m) = 1 then
    if right : (1 - m) * value = 1 then .ok ⟨value, left, right⟩
    else .error ⟨.invalidInverse, "inverse", "right"⟩
  else .error ⟨.invalidInverse, "inverse", "left"⟩

theorem checkInverse_value {n : Nat} {m value : RationalMatrix n n} {inv : Inverse m}
    (checked : checkInverse m value = .ok inv) : inv.value = value := by
  unfold checkInverse at checked
  split at checked
  · split at checked
    · cases checked
      rfl
    · cases checked
  · cases checked

/-- Checks the ports and reports the first error in declaration order: empty or
repeated IDs and names across all ports, their roles (`.state` loop ports,
`.input` or `.parameter` external ports, `.output` outputs), then the left and
right products of the supplied inverse. -/
def Declaration.validate {n d o : Nat} (a : Declaration n d o) :
    Except Model.Diagnostic Unit := do
  let ports := List.ofFn a.loop ++ List.ofFn a.external ++ List.ofFn a.outputs
  for p in ports do
    require (!p.id.isEmpty) .emptyId "ports" p.name
    require (!p.name.isEmpty) .emptyName "ports" p.id
  checkUnique (ports.map Port.id) .duplicateId "ports"
  checkUnique (ports.map Port.name) .duplicateName "ports"
  for p in List.ofFn a.loop do
    require (p.role == .state) .unsupportedRole p.id p.name
  for p in List.ofFn a.external do
    require ([.input, .parameter].contains p.role) .unsupportedRole p.id p.name
  for p in List.ofFn a.outputs do
    require (p.role == .output) .unsupportedRole p.id p.name
  let _ ← checkInverse a.problem.matrix a.inverse

/-- An accepted declaration: validated, with the supplied inverse checked. -/
structure AlgebraicModel {n d o : Nat} (a : Declaration n d o) where
  valid : a.validate = .ok ()
  inverse : Inverse a.problem.matrix
  supplied : inverse.value = a.inverse

/-- Validate, then carry the checked inverse. The second check cannot fail after
validation; it is repeated here to carry the evidence. -/
def Declaration.compile {n d o : Nat} (a : Declaration n d o) :
    Except Model.Diagnostic (AlgebraicModel a) :=
  match hv : a.validate with
  | .error error => .error error
  | .ok () =>
    match hi : checkInverse a.problem.matrix a.inverse with
    -- Unreachable: `validate` already refused a failing product.
    | .error error => .error error
    | .ok inv => .ok ⟨hv, inv, checkInverse_value hi⟩

/-- A loop with no inverse of `1 - M` has no accepted declaration. -/
theorem AlgebraicModel.singular {n d o : Nat} (a : Declaration n d o)
    (singular : ¬ Nonempty (Inverse a.problem.matrix)) : IsEmpty (AlgebraicModel a) :=
  ⟨fun m => singular ⟨m.inverse⟩⟩

/-- The compiled loop circuit, over coordinates [loop, external]. -/
def Declaration.loopCircuit {n d o : Nat} (a : Declaration n d o) : Circuit (n + d) n :=
  a.problem.loopAffine.circuit

/-- The compiled output circuit, over coordinates [loop, external]. -/
def Declaration.outputCircuit {n d o : Nat} (a : Declaration n d o) : Circuit (n + d) o :=
  a.problem.output.circuit

/-- The eliminated feedforward circuit, from the external inputs alone. -/
def AlgebraicModel.circuit {n d o : Nat} {a : Declaration n d o} (_ : AlgebraicModel a) :
    Circuit d o :=
  a.problem.eliminatedCircuit a.inverse

/-- The declaration's source relation: some loop point in the domain solves the
ordered source loop equations, and the ordered source outputs read `y`. -/
def Declaration.Solves {n d o : Nat} (a : Declaration n d o) (u : Point d) (y : Point o) :
    Prop :=
  Algebraic.Solves a.problem.loopAffine.expression a.problem.output.expression a.domain u y

/-- **Every input.** The source equations hold exactly when the compiled loop and
output circuits are related, for every declaration, accepted or not. No
existence or uniqueness is asserted. -/
theorem Declaration.solves_iff_rel {n d o : Nat} (a : Declaration n d o) (u : Point d)
    (y : Point o) : a.Solves u y ↔ Rel a.loopCircuit a.outputCircuit a.domain u y :=
  compile_correct _ _ a.domain u y

/-- **Admitted inputs.** For an accepted declaration and an admitted input,
exactly one loop point in the domain solves the loop, and the relation holds of
exactly the eliminated circuit's output. The membership obligation is the
declaration's own. -/
theorem AlgebraicModel.eliminate_correct {n d o : Nat} {a : Declaration n d o}
    (m : AlgebraicModel a) (u : Point d) (hu : a.admitted u) :
    (∃! z, a.domain z ∧ a.loopCircuit.run (pointAppend z u) = z) ∧
      ∀ y, Rel a.loopCircuit a.outputCircuit a.domain u y ↔ y = m.circuit.run u := by
  have membership := a.membership
  rw [← m.supplied] at membership
  have := a.problem.eliminate_correct m.inverse a.domain a.admitted membership u hu
  rw [m.supplied] at this
  exact this

/-- The two theorems combined: on an admitted input, the source equations hold of
exactly the eliminated circuit's output. -/
theorem AlgebraicModel.solves_iff_eliminated {n d o : Nat} {a : Declaration n d o}
    (m : AlgebraicModel a) (u : Point d) (hu : a.admitted u) (y : Point o) :
    a.Solves u y ↔ y = m.circuit.run u := by
  rw [a.solves_iff_rel]
  exact (m.eliminate_correct u hu).2 y

#print axioms checkInverse_value
#print axioms Declaration.coordinates_loop
#print axioms Declaration.coordinates_external
#print axioms Declaration.solves_iff_rel
#print axioms AlgebraicModel.eliminate_correct
#print axioms AlgebraicModel.solves_iff_eliminated
end Gimle.Asgard.Algebraic
