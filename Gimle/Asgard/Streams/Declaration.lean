import Gimle.Asgard.Model.Declaration
import Gimle.Asgard.Streams.Named

/-! # Declared stream equations

A stream declaration names

* its **basis**, which is part of the model's identity: an OGF and an EGF
  declaration are different values, and their equations resolve to expressions
  of different types (`Expr .ogf …` and `Expr .egf …`);
* its **ordered axes**, by stable ID. The position of an axis is its position in
  the declared list; nothing sorts or renames axes, so a permuted declaration
  resolves to permuted indices (`Equation.resolve_ids`);
* its **inputs**: every unknown is a `.state` port, every boundary profile a
  `.boundary` port, and anything else a `.parameter` port read as an arbitrary
  external stream;
* its **equations** `D_along unknown = rhs`, each with a declared boundary input
  on the named axis `along`.

The *boundary* of an equation along axis `i` is the **whole coefficient slice**
`{α | α_i = 0}` of the unknown: the unknown and the boundary input agree there,
and every other coefficient of the boundary input is ignored by the boundary
condition (a right-hand side may still read it). That is the same
slice `integral` reads from its second argument (`integral_boundary`).

The stream-equation pass is `Equation.solves_iff_integral`: a stream point
solves an accepted equation exactly when its unknown is
`integral(rhs, boundary)` along the declared axis, where the right-hand side's
value is read through its compiled relation, the one `Context.compiled_iff`
characterizes. `Equation.solves_iff_rebuilt` states the same for the single
compiled reconstruction circuit. Neither asserts that a solution exists or is
unique.

A series substitution is accepted only where its `CanCompose` side condition is
**established** syntactically (`NamedExpr.unestablished`,
`NamedExpr.established_defined`); anywhere else, including a branch whose value
is discarded or multiplied by zero, the declaration is refused with
`unestablishedCompose`. Every accepted right-hand side is therefore defined on
every input (`StreamModel.rhs_defined`). -/
namespace Gimle.Asgard.Streams

/-! ## Constant coefficients -/

/-- The constant coefficient of the decoded series is the raw coefficient at `0`,
in either basis (`0! ⋯ 0! = 1`). -/
theorem constantCoeff_decode {d : Nat} (basis : Basis) (a : Stream d) :
    MvPowerSeries.constantCoeff (decode basis a) = a 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_apply]
  cases basis with
  | ogf => rfl
  | egf => simp [decode, factorial]

/-- `CanCompose` is exactly a zero raw coefficient at the origin. -/
theorem canCompose_iff {d : Nat} (basis : Basis) (a : Stream d) :
    CanCompose basis a ↔ a 0 = 0 := by
  rw [CanCompose, constantCoeff_decode]

theorem constant_zero {d : Nat} (basis : Basis) (q : ℚ) : constant (d := d) basis q 0 = q := by
  rw [← constantCoeff_decode basis (constant basis q), constant, decode_encode]
  simp

theorem axisVariable_zero {d : Nat} (basis : Basis) (axis : Fin d) :
    axisVariable basis axis 0 = 0 := by
  rw [← constantCoeff_decode basis (axisVariable basis axis), axisVariable, decode_encode]
  simp

theorem product_zero {d : Nat} (basis : Basis) (a b : Stream d) :
    product basis a b 0 = a 0 * b 0 := by
  rw [← constantCoeff_decode basis (product basis a b), decode_product, map_mul,
    constantCoeff_decode, constantCoeff_decode]

theorem integral_zero {d : Nat} (basis : Basis) (axis : Fin d) (a boundary : Stream d) :
    integral basis axis a boundary 0 = boundary 0 :=
  integral_boundary basis axis a boundary 0 rfl

/-! ## Established substitution -/

/-- Syntactic evidence that a source expression has zero constant coefficient:
the constant `0`, an axis variable, a sum of such, a product with such a factor,
or an integral whose boundary is such. Anything else, including every input, is
not evidence. -/
def NamedExpr.composable : NamedExpr → Bool
  | .constant q => q == 0
  | .axisVariable _ => true
  | .binary .add a b => a.composable && b.composable
  | .binary .product a b => a.composable || b.composable
  | .binary (.integral _) _ b => b.composable
  | _ => false

/-- The axis ID of the first series substitution, children first, whose inner
argument is not `composable`; `none` when every substitution is established. -/
def NamedExpr.unestablished : NamedExpr → Option String
  | .input _ | .constant _ | .axisVariable _ => none
  | .unary _ a => a.unestablished
  | .binary op a b =>
    match a.unestablished, b.unestablished, op with
    | some axis, _, _ => some axis
    | none, some axis, _ => some axis
    | none, none, .seriesCompose axis => if b.composable then none else some axis
    | none, none, _ => none

theorem NamedExpr.resolve_unary {basis : Basis} {d n : Nat} (axes : String → Option (Fin d))
    (inputs : String → Option (Expr basis d n)) (op : NamedUnary) (a : NamedExpr)
    (r : Expr basis d n) (found : (NamedExpr.unary op a).resolve axes inputs = some r) :
    ∃ op' a', op.resolve axes = some op' ∧ a.resolve axes inputs = some a' ∧
      r = .unary op' a' := by
  simp only [resolve, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at found
  obtain ⟨op', hop, a', ha, rfl⟩ := found
  exact ⟨op', a', hop, ha, rfl⟩

theorem NamedExpr.resolve_binary {basis : Basis} {d n : Nat} (axes : String → Option (Fin d))
    (inputs : String → Option (Expr basis d n)) (op : NamedBinary) (a b : NamedExpr)
    (r : Expr basis d n) (found : (NamedExpr.binary op a b).resolve axes inputs = some r) :
    ∃ op' a' b', op.resolve axes = some op' ∧ a.resolve axes inputs = some a' ∧
      b.resolve axes inputs = some b' ∧ r = .binary op' a' b' := by
  simp only [resolve, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at found
  obtain ⟨op', hop, a', ha, b', hb, rfl⟩ := found
  exact ⟨op', a', b', hop, ha, hb, rfl⟩

/-- A `composable` expression resolves to one whose value has a zero constant
coefficient on every input. -/
theorem NamedExpr.composable_sound {basis : Basis} {d n : Nat} (axes : String → Option (Fin d))
    (inputs : String → Option (Expr basis d n)) (x : StreamPoint d n) :
    ∀ (e : NamedExpr) (r : Expr basis d n), e.composable = true →
      e.resolve axes inputs = some r → r.value x 0 = 0
  | .input _, _, zero, _ => by simp [composable] at zero
  | .constant q, r, zero, found => by
    simp only [resolve, Option.some.injEq] at found
    subst found
    simpa [composable, Expr.value, constant_zero] using zero
  | .axisVariable i, r, _, found => by
    simp only [resolve, Option.map_eq_some_iff] at found
    obtain ⟨j, _, rfl⟩ := found
    exact axisVariable_zero basis j
  | .unary _ _, _, zero, _ => by simp [composable] at zero
  | .binary op a b, r, zero, found => by
    obtain ⟨op', a', b', hop, ha, hb, rfl⟩ := resolve_binary axes inputs op a b r found
    cases op with
    | add =>
      simp only [composable, Bool.and_eq_true] at zero
      simp only [NamedBinary.resolve, Option.some.injEq] at hop
      subst hop
      change a'.value x 0 + b'.value x 0 = 0
      rw [composable_sound axes inputs x a a' zero.1 ha,
        composable_sound axes inputs x b b' zero.2 hb, add_zero]
    | product =>
      simp only [composable, Bool.or_eq_true] at zero
      simp only [NamedBinary.resolve, Option.some.injEq] at hop
      subst hop
      change product basis (a'.value x) (b'.value x) 0 = 0
      rw [product_zero]
      rcases zero with zero | zero
      · rw [composable_sound axes inputs x a a' zero ha, zero_mul]
      · rw [composable_sound axes inputs x b b' zero hb, mul_zero]
    | integral i =>
      simp only [composable] at zero
      simp only [NamedBinary.resolve, Option.map_eq_some_iff] at hop
      obtain ⟨j, _, rfl⟩ := hop
      change integral basis j (a'.value x) (b'.value x) 0 = 0
      rw [integral_zero, composable_sound axes inputs x b b' zero hb]
    | seriesCompose _ => simp [composable] at zero

theorem NamedExpr.unestablished_binary {op : NamedBinary} {a b : NamedExpr}
    (none_found : (NamedExpr.binary op a b).unestablished = none) :
    a.unestablished = none ∧ b.unestablished = none ∧
      ∀ axis, op = .seriesCompose axis → b.composable = true := by
  cases ha : a.unestablished <;> cases hb : b.unestablished <;> cases op <;>
    simp_all [unestablished]

/-- An expression whose every substitution is established resolves, over inputs
that are themselves defined, to an expression defined on that input. -/
theorem NamedExpr.established_defined {basis : Basis} {d n : Nat}
    (axes : String → Option (Fin d)) (inputs : String → Option (Expr basis d n))
    (x : StreamPoint d n) (defined : ∀ id r, inputs id = some r → r.Defined x) :
    ∀ (e : NamedExpr) (r : Expr basis d n), e.unestablished = none →
      e.resolve axes inputs = some r → r.Defined x
  | .input i, r, _, found => defined i r found
  | .constant _, r, _, found => by
    simp only [resolve, Option.some.injEq] at found
    subst found
    trivial
  | .axisVariable _, r, _, found => by
    simp only [resolve, Option.map_eq_some_iff] at found
    obtain ⟨_, _, rfl⟩ := found
    trivial
  | .unary op a, r, none_found, found => by
    obtain ⟨_, a', _, ha, rfl⟩ := resolve_unary axes inputs op a r found
    exact established_defined axes inputs x defined a a' none_found ha
  | .binary op a b, r, none_found, found => by
    obtain ⟨op', a', b', hop, ha, hb, rfl⟩ := resolve_binary axes inputs op a b r found
    obtain ⟨na, nb, composed⟩ := unestablished_binary none_found
    refine ⟨⟨established_defined axes inputs x defined a a' na ha,
      established_defined axes inputs x defined b b' nb hb⟩, ?_⟩
    cases op with
    | add | product =>
      simp only [NamedBinary.resolve, Option.some.injEq] at hop
      subst hop
      trivial
    | integral _ =>
      simp only [NamedBinary.resolve, Option.map_eq_some_iff] at hop
      obtain ⟨_, _, rfl⟩ := hop
      trivial
    | seriesCompose axis =>
      simp only [NamedBinary.resolve, Option.map_eq_some_iff] at hop
      obtain ⟨_, _, rfl⟩ := hop
      exact (canCompose_iff basis _).mpr
        (composable_sound axes inputs x b b' (composed axis rfl) hb)

/-- Under a context, an established expression is defined on every point. -/
theorem Context.established_defined (c : Context) (basis : Basis) (e : NamedExpr)
    (r : Expr basis c.axes.length c.inputs.length) (accepted : c.resolve basis e = some r)
    (established : e.unestablished = none) (x : StreamPoint c.axes.length c.inputs.length) :
    r.Defined x := by
  unfold Context.resolve at accepted
  split at accepted
  · refine NamedExpr.established_defined _ _ x ?_ e r established accepted
    intro id r found
    simp only [Option.map_eq_some_iff] at found
    obtain ⟨_, _, rfl⟩ := found
    trivial
  · cases accepted

/-! ## The stream-equation relation -/

/-- **One equation on streams.** `u` has derivative `f` along `axis` and agrees
with `b` on the whole zero slice along `axis` exactly when `u = integral(f, b)`
along `axis`. Both directions; no existence or uniqueness is claimed. -/
theorem derivative_iff_integral {d : Nat} (basis : Basis) (axis : Fin d) (u f b : Stream d) :
    (derivative basis axis u = f ∧ ∀ n : Index d, n axis = 0 → u n = b n) ↔
      u = integral basis axis f b := by
  constructor
  · rintro ⟨rfl, slice⟩
    funext n
    by_cases zero : n axis = 0
    · rw [integral_boundary _ _ _ _ _ zero, slice n zero]
    · conv_lhs => rw [← integral_derivative basis axis u]
      simp [integral, zero]
  · rintro rfl
    exact ⟨derivative_integral basis axis f b,
      fun n zero => integral_boundary basis axis f b n zero⟩

/-! ## Declarations -/

/-- `D_along unknown = rhs`, where `unknown` equals the input `boundary` on the
whole zero slice along the axis `along`. All three are stable IDs. -/
structure Equation where
  unknown : String
  along : String
  boundary : String
  rhs : NamedExpr
  deriving Repr, DecidableEq

/-- A stream declaration. The basis is a field, so it is part of the value's
identity; axes and inputs are ordered lists of stable IDs. -/
structure Declaration where
  basis : Basis
  axes : List Axis
  inputs : List Polynomial.Port
  equations : List Equation
  deriving Repr, DecidableEq

/-- The named context the right-hand sides resolve in, in declared order. -/
def Declaration.context (s : Declaration) : Context := ⟨s.axes, s.inputs⟩

/-- Input IDs a source expression reads, in source order. -/
def NamedExpr.inputRefs : NamedExpr → List String
  | .input id => [id]
  | .constant _ | .axisVariable _ => []
  | .unary _ a => a.inputRefs
  | .binary _ a b => a.inputRefs ++ b.inputRefs

/-- Axis IDs a source expression names, in source order, operator first. -/
def NamedExpr.axisRefs : NamedExpr → List String
  | .input _ | .constant _ => []
  | .axisVariable id => [id]
  | .unary (.derivative id) a => id :: a.axisRefs
  | .binary op a b =>
    (match op with
      | .add | .product => []
      | .integral id | .seriesCompose id => [id]) ++ a.axisRefs ++ b.axisRefs

private def require (condition : Bool) (code : Model.ErrorCode) (site reference : String) :
    Except Model.Diagnostic Unit :=
  if condition then .ok () else .error ⟨code, site, reference⟩

private def checkUnique (values : List String) (code : Model.ErrorCode) (site : String) :
    Except Model.Diagnostic Unit := do
  let mut seen := []
  for value in values do
    require (!seen.contains value) code site value
    seen := value :: seen

private def checkInput (s : Declaration) (site id : String) (role : Polynomial.PortRole) :
    Except Model.Diagnostic Unit :=
  match s.inputs.find? (·.id == id) with
  | none => .error ⟨.unknownReference, site, id⟩
  | some p => require (p.role == role) .unsupportedRole site id

/-- Checks the declaration's shape and reports the first error in declaration
order: empty or repeated axis and input IDs and names, input roles, each
equation's unknown (a `.state` input), axis and boundary (a `.boundary` input),
the names its right-hand side reads, unestablished series substitutions, and
that unknowns and boundaries are each bound by exactly one equation. -/
def Declaration.validate (s : Declaration) : Except Model.Diagnostic Unit := do
  for a in s.axes do
    require (!a.id.isEmpty) .emptyId "axes" a.name
    require (!a.name.isEmpty) .emptyName "axes" a.id
  checkUnique (s.axes.map Axis.id) .duplicateId "axes"
  checkUnique (s.axes.map Axis.name) .duplicateName "axes"
  for p in s.inputs do
    require (!p.id.isEmpty) .emptyId "inputs" p.name
    require (!p.name.isEmpty) .emptyName "inputs" p.id
    require ([.state, .boundary, .parameter].contains p.role) .unsupportedRole p.id p.name
  checkUnique (s.inputs.map Polynomial.Port.id) .duplicateId "inputs"
  checkUnique (s.inputs.map Polynomial.Port.name) .duplicateName "inputs"
  for eq in s.equations do
    checkInput s "equations" eq.unknown .state
    require (s.axes.any (·.id == eq.along)) .unknownReference eq.unknown eq.along
    checkInput s eq.unknown eq.boundary .boundary
    for id in eq.rhs.inputRefs do
      require (s.inputs.any (·.id == id)) .unknownReference eq.unknown id
    for id in eq.rhs.axisRefs do
      require (s.axes.any (·.id == id)) .unknownReference eq.unknown id
    match eq.rhs.unestablished with
    | some axis => throw ⟨.unestablishedCompose, eq.unknown, axis⟩
    | none => pure ()
  checkUnique (s.equations.map Equation.unknown) .duplicateBinding "equations"
  checkUnique (s.equations.map Equation.boundary) .duplicateBinding "boundaries"
  for p in s.inputs do
    if p.role == .state then
      require (s.equations.any (·.unknown == p.id)) .missingBinding "equations" p.id
    if p.role == .boundary then
      require (s.equations.any (·.boundary == p.id)) .missingBinding "boundaries" p.id

/-! ## Resolution -/

/-- An equation with its IDs resolved to declared positions. -/
structure ResolvedEquation (basis : Basis) (d n : Nat) where
  unknown : Fin n
  along : Fin d
  boundary : Fin n
  rhs : Expr basis d n
  deriving Repr, DecidableEq

/-- Resolve an equation's IDs in declared order; `none` if any name is missing
or the context is invalid (for example, a repeated axis ID). -/
def Equation.resolve (c : Context) (basis : Basis) (eq : Equation) :
    Option (ResolvedEquation basis c.axes.length c.inputs.length) := do
  return ⟨← c.input eq.unknown, ← c.axis eq.along, ← c.input eq.boundary,
    ← c.resolve basis eq.rhs⟩

/-- Resolve every equation, in declared order. -/
def Declaration.resolve (s : Declaration) :
    Option (List (ResolvedEquation s.basis s.context.axes.length s.context.inputs.length)) :=
  s.equations.mapM (Equation.resolve s.context s.basis)

/-- The reconstruction `integral(rhs, boundary)` along the equation's axis. -/
def ResolvedEquation.rebuilt {basis : Basis} {d n : Nat} (r : ResolvedEquation basis d n) :
    Expr basis d n := .binary (.integral r.along) r.rhs (.input r.boundary)

/-- The observed circuit `[rhs, integral(rhs, boundary)]`, the shape of the
hand-built formal heat circuit. -/
def ResolvedEquation.circuit {basis : Basis} {d n : Nat} (r : ResolvedEquation basis d n) :
    Circuit basis d n 2 := r.rhs.compile.pair r.rebuilt.compile

theorem Equation.resolve_some (c : Context) (basis : Basis) (eq : Equation)
    (r : ResolvedEquation basis c.axes.length c.inputs.length)
    (accepted : eq.resolve c basis = some r) :
    c.input eq.unknown = some r.unknown ∧ c.axis eq.along = some r.along ∧
      c.input eq.boundary = some r.boundary ∧ c.resolve basis eq.rhs = some r.rhs := by
  simp only [resolve, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.some.injEq] at accepted
  obtain ⟨u, hu, a, ha, b, hb, e, he, rfl⟩ := accepted
  exact ⟨hu, ha, hb, he⟩

theorem Context.input_sound (c : Context) (id : String) (i : Fin c.inputs.length)
    (found : c.input id = some i) : c.inputs[i].id = id := by
  unfold input at found
  split at found
  · cases h : Polynomial.lookupIndex (c.inputs.map Polynomial.Port.id) id with
    | none => simp [h] at found
    | some j =>
      simp [h] at found
      subst i
      simpa using Polynomial.lookupIndex_sound (c.inputs.map Polynomial.Port.id) id j h
  · simp at found

/-- **Declared order is kept.** A resolved equation reads the axis and inputs at
the declared positions of its IDs, so permuting the declaration permutes the
indices and never the meaning of an ID. -/
theorem Equation.resolve_ids (c : Context) (basis : Basis) (eq : Equation)
    (r : ResolvedEquation basis c.axes.length c.inputs.length)
    (accepted : eq.resolve c basis = some r) :
    c.axes[r.along].id = eq.along ∧ c.inputs[r.unknown].id = eq.unknown ∧
      c.inputs[r.boundary].id = eq.boundary := by
  obtain ⟨hu, ha, hb, _⟩ := resolve_some c basis eq r accepted
  exact ⟨c.axis_sound _ _ ha, c.input_sound _ _ hu, c.input_sound _ _ hb⟩

/-! ## Solution sets -/

/-- The source relation of one equation, stated through the independent named
meaning of its right-hand side: the named value is defined, it is the unknown's
derivative along the declared axis, and the unknown equals the boundary input on
the whole zero slice along that axis. -/
def Equation.Solves (c : Context) (basis : Basis) (eq : Equation)
    (x : StreamPoint c.axes.length c.inputs.length) : Prop :=
  ∃ unknown along boundary value domain,
    c.input eq.unknown = some unknown ∧ c.axis eq.along = some along ∧
    c.input eq.boundary = some boundary ∧
    c.meaning basis eq.rhs x = some (value, domain) ∧ domain ∧
    derivative basis along (x unknown) = value ∧
    ∀ k : Index c.axes.length, k along = 0 → x unknown k = x boundary k

/-- **The stream-equation pass.** A point solves an accepted equation
`D_t u = F(u)` with boundary `b` exactly when `u = integral(F(u), b)` along the
declared axis, where `F(u)` is the output of the right-hand side's compiled
circuit (`Context.compiled_iff`). Both directions. -/
theorem Equation.solves_iff_integral (c : Context) (basis : Basis) (eq : Equation)
    (r : ResolvedEquation basis c.axes.length c.inputs.length)
    (accepted : eq.resolve c basis = some r) (x : StreamPoint c.axes.length c.inputs.length) :
    eq.Solves c basis x ↔ ∃ value, r.rhs.compile.Rel x ![value] ∧
      x r.unknown = integral basis r.along value (x r.boundary) := by
  obtain ⟨hu, ha, hb, he⟩ := resolve_some c basis eq r accepted
  simp only [Solves, hu, ha, hb, Option.some.injEq]
  constructor
  · rintro ⟨_, _, _, value, domain, rfl, rfl, rfl, meaning, holds, slope, slice⟩
    refine ⟨value, ?_, (derivative_iff_integral basis _ _ _ _).mp ⟨slope, slice⟩⟩
    exact (c.compiled_iff basis eq.rhs r.rhs he x ![value]).mpr ⟨value, domain, meaning, holds, rfl⟩
  · rintro ⟨value, rel, rebuilt⟩
    obtain ⟨v, domain, meaning, holds, same⟩ :=
      (c.compiled_iff basis eq.rhs r.rhs he x ![value]).mp rel
    have same : value = v := congrFun same 0
    subst same
    obtain ⟨slope, slice⟩ := (derivative_iff_integral basis _ _ _ _).mpr rebuilt
    exact ⟨_, _, _, value, domain, rfl, rfl, rfl, meaning, holds, slope, slice⟩

/-- The same solution set, as the single compiled reconstruction circuit: `u`
solves the equation exactly when `integral(rhs, boundary)` returns `u`. -/
theorem Equation.solves_iff_rebuilt (c : Context) (basis : Basis) (eq : Equation)
    (r : ResolvedEquation basis c.axes.length c.inputs.length)
    (accepted : eq.resolve c basis = some r) (x : StreamPoint c.axes.length c.inputs.length) :
    eq.Solves c basis x ↔ r.rebuilt.compile.Rel x ![x r.unknown] := by
  rw [solves_iff_integral c basis eq r accepted, Expr.compile_rel]
  simp only [Expr.compile_rel, ResolvedEquation.rebuilt, Expr.Defined, Binary.Domain, and_true,
    Expr.value, Binary.value]
  constructor
  · rintro ⟨value, ⟨defined, same⟩, rebuilt⟩
    have same : value = r.rhs.value x := congrFun same 0
    subst same
    exact ⟨defined, by rw [← rebuilt]⟩
  · rintro ⟨defined, rebuilt⟩
    exact ⟨_, ⟨defined, rfl⟩, congrFun rebuilt 0⟩

/-- Every equation of the declaration holds. -/
def Declaration.Solves (s : Declaration)
    (x : StreamPoint s.context.axes.length s.context.inputs.length) : Prop :=
  ∀ eq ∈ s.equations, eq.Solves s.context s.basis x

/-- An accepted declaration: validated, resolved in declared order, and with
every series substitution established. -/
structure StreamModel (s : Declaration) where
  valid : s.validate = .ok ()
  equations : List (ResolvedEquation s.basis s.context.axes.length s.context.inputs.length)
  resolved : s.resolve = some equations
  established : ∀ eq ∈ s.equations, eq.rhs.unestablished = none

/-- Validate, resolve and check substitutions. The last two cannot fail after
validation; they are rechecked here to carry the evidence. -/
def Declaration.compile (s : Declaration) : Except Model.Diagnostic (StreamModel s) :=
  match hv : s.validate with
  | .error error => .error error
  | .ok () =>
    match hr : s.resolve with
    | none => .error ⟨.incompleteResolution, "equations", "resolution"⟩
    | some rs =>
      if he : ∀ eq ∈ s.equations, eq.rhs.unestablished = none then .ok ⟨hv, rs, hr, he⟩
      -- Unreachable: `validate` already refused every unestablished substitution.
      else .error ⟨.unestablishedCompose, "equations", "substitution"⟩

private theorem forall₂_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → List.Forall₂ (fun a b => f a = some b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact .nil
  | a :: l, l', h => by
    simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨b, hb, bs, hbs, rfl⟩ := h
    exact .cons hb (forall₂_of_mapM hbs)

private theorem forall_iff_of_forall₂ {α β : Type} {R : α → β → Prop} {P : α → Prop}
    {Q : β → Prop} (link : ∀ a b, R a b → (P a ↔ Q b)) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ((∀ a ∈ l, P a) ↔ ∀ b ∈ l', Q b)
  | _, _, .nil => by simp
  | _, _, .cons h rest => by
    simp only [List.forall_mem_cons]
    rw [link _ _ h, forall_iff_of_forall₂ link rest]

private theorem exists_of_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ b ∈ l', ∃ a ∈ l, R a b
  | _, _, .nil, _, member => by simp at member
  | _, _, .cons h rest, b, member => by
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨_, List.mem_cons_self .., h⟩
    · obtain ⟨a, ha, hab⟩ := exists_of_forall₂ rest b member
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

/-- Every accepted right-hand side is defined on every point: all its series
substitutions are established. -/
theorem StreamModel.rhs_defined {s : Declaration} (m : StreamModel s) :
    ∀ r ∈ m.equations, ∀ x, r.rhs.Defined x := by
  intro r member x
  obtain ⟨eq, eqMember, accepted⟩ := exists_of_forall₂ (forall₂_of_mapM m.resolved) r member
  exact Context.established_defined _ _ eq.rhs r.rhs
    (Equation.resolve_some _ _ eq r accepted).2.2.2 (m.established eq eqMember) x

/-- **The declaration's solution set** is exactly the set of points each of
whose reconstruction circuits returns its unknown. -/
theorem StreamModel.solves_iff {s : Declaration} (m : StreamModel s)
    (x : StreamPoint s.context.axes.length s.context.inputs.length) :
    s.Solves x ↔ ∀ r ∈ m.equations, r.rebuilt.compile.Rel x ![x r.unknown] :=
  forall_iff_of_forall₂ (fun eq r accepted => Equation.solves_iff_rebuilt _ _ eq r accepted x)
    (forall₂_of_mapM m.resolved)

/-- With no domain left, the solution set is the fixed-point form
`u = integral(F(u), b)` of every equation, along its declared axis. -/
theorem StreamModel.solves_iff_integral {s : Declaration} (m : StreamModel s)
    (x : StreamPoint s.context.axes.length s.context.inputs.length) :
    s.Solves x ↔ ∀ r ∈ m.equations,
      x r.unknown = integral s.basis r.along (r.rhs.value x) (x r.boundary) := by
  rw [m.solves_iff x]
  apply forall_congr'
  intro r
  apply forall_congr'
  intro member
  rw [Expr.compile_rel]
  simp only [ResolvedEquation.rebuilt, Expr.Defined, Binary.Domain, and_true, Expr.value,
    Binary.value]
  constructor
  · rintro ⟨_, same⟩
    exact congrFun same 0
  · intro same
    exact ⟨m.rhs_defined r member x, by rw [← same]⟩

#print axioms constantCoeff_decode
#print axioms NamedExpr.composable_sound
#print axioms NamedExpr.established_defined
#print axioms derivative_iff_integral
#print axioms Equation.resolve_ids
#print axioms Equation.solves_iff_integral
#print axioms Equation.solves_iff_rebuilt
#print axioms StreamModel.rhs_defined
#print axioms StreamModel.solves_iff
#print axioms StreamModel.solves_iff_integral
end Gimle.Asgard.Streams
