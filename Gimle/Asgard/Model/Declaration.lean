import Gimle.Asgard.Dynamics.Named

/-! Common deterministic declarations. Validation checks metadata and references,
not dependency order, solvability or compilation. The original AST is retained.
The polynomial and continuous interpretations remain distinct. -/
namespace Gimle.Asgard.Model
open Polynomial

/-- A fixed exact value, bound by stable port ID rather than display name. -/
structure RationalBinding where
  id : String
  value : ℚ
  deriving Repr, DecidableEq

/-- An ordered observation has its own external identity and selects a source ID.
Display names are unique among observations, but may match source names. -/
structure Observation where
  port : Port
  sourceId : String
  deriving Repr, DecidableEq

structure Body where
  program : Program
  parameters : List RationalBinding := []
  observations : List Observation := []
  deriving Repr, DecidableEq

/-- One autonomous continuous evolution axis, with fixed rational initial data.
The intended time domain is the forward half-line beginning at `start`. -/
structure Evolution where
  states : List Dynamics.StateBinding
  initialPorts : List Port
  initialValues : List RationalBinding
  axis : Dynamics.Axis
  evolveAlong : String
  start : ℚ
  deriving Repr, DecidableEq

/-- A declared time-varying driver of a continuous evolution: the `.driver`
port `driverId`, read as an arbitrary external signal on the evolution axis,
and, only when it is declared differentiable, the `.driver` port `derivativeId`,
which the driven relation binds to the actual derivative of that signal. -/
structure DriverBinding where
  driverId : String
  derivativeId : Option String := none
  deriving Repr, DecidableEq

/-- The driver ports in coordinate order: each driver, then its derivative port
when it declares one. -/
def DriverBinding.ports (ds : List DriverBinding) : List String :=
  ds.flatMap fun d => d.driverId :: d.derivativeId.toList

inductive Declaration where
  | polynomial (body : Body)
  | continuous (body : Body) (evolution : Evolution)
  /-- A continuous evolution with declared drivers. Nothing is inferred: every
  `.driver` port is declared here, and only declared ports may be drivers. -/
  | driven (body : Body) (evolution : Evolution) (drivers : List DriverBinding)
  deriving Repr, DecidableEq

/-- Inspect the exact original named program, without reordering or substitution. -/
def Declaration.body : Declaration → Body
  | .polynomial b => b
  | .continuous b _ => b
  | .driven b _ _ => b

/-- Metadata projection to the existing continuous interface. This does not
schedule equations, specialize parameters, or invoke System.prepare. System
treats parameters as external signals and does not carry fixed values or start
time; this raw view alone does not retain the full declaration semantics. Nor
does it name the drivers of a driven declaration, which `Model.Driven` reads
from its `DriverBinding`s. -/
def Evolution.system (e : Evolution) (b : Body) : Dynamics.System where
  program := b.program
  states := e.states
  externalIds := (b.program.inputs.filter (·.role == .parameter)).map Port.id
  initialPorts := e.initialPorts
  axis := e.axis
  evolveAlong := e.evolveAlong

inductive ErrorCode where
  | emptyId | emptyName | duplicateId | duplicateName | unsupportedRole
  | unknownReference | duplicateBinding | missingBinding | wrongAxis
  | cyclicDependency | incompleteResolution
  -- Differential isolation (`Model.Differential`); each names a form outside
  -- the accepted differential fragment, never an unsatisfiable model.
  | missingDerivative | competingDerivative | repeatedDerivative
  | nonlinearDerivative | higherOrderDerivative | mixedDerivative
  | unsupportedDerivative | zeroScale
  -- Source integrals (`Model.Integral`): an integral that no inverse rewrite
  -- removes and no declared integral state reads, or one outside an evolution
  -- declaration.
  | unsupportedIntegral
  -- A declared integral state whose declared initial value is not `0`.
  | nonzeroInitial
  -- Stream declarations (`Streams.Declaration`): a series substitution whose
  -- inner argument is not syntactically known to have zero constant coefficient.
  -- Like the codes above, it names an unsupported form, never an unsatisfiable
  -- model.
  | unestablishedCompose
  deriving Repr, DecidableEq, BEq

/-- `site` identifies the declaration being checked; `reference` identifies the
bad name or ID, or for `unsupportedIntegral` the reason (`axis`, `integrand`,
`no inverse rewrite`). Validation reports the first error in declaration order. -/
structure Diagnostic where
  code : ErrorCode
  site : String
  reference : String
  deriving Repr, DecidableEq, BEq

private def require (condition : Bool) (code : ErrorCode) (site reference : String) :
    Except Diagnostic Unit :=
  if condition then .ok () else .error ⟨code, site, reference⟩

private def checkUnique (values : List String) (code : ErrorCode) (site : String) :
    Except Diagnostic Unit := do
  let mut seen := []
  for value in values do
    require (!seen.contains value) code site value
    seen := value :: seen

private def checkPorts (ports : List Port) (site : String) : Except Diagnostic Unit := do
  for p in ports do
    require (!p.id.isEmpty) .emptyId site p.name
    require (!p.name.isEmpty) .emptyName site p.id
  checkUnique (ports.map Port.id) .duplicateId site
  checkUnique (ports.map Port.name) .duplicateName site

private def checkRole (p : Port) (allowed : List PortRole) : Except Diagnostic Unit :=
  require (allowed.contains p.role) .unsupportedRole p.id p.name

private def checkExpr (names : List String) (site : String) : NamedExpr → Except Diagnostic Unit
  | .var name => require (names.contains name) .unknownReference site name
  | .constant _ => .ok ()
  | .add a b | .mul a b => do checkExpr names site a; checkExpr names site b
  | .neg a => checkExpr names site a

/-- Bindings must cover exactly the declared IDs, including unused parameters. -/
private def checkValues (ports : List Port) (values : List RationalBinding)
    (site : String) : Except Diagnostic Unit := do
  checkUnique (values.map RationalBinding.id) .duplicateBinding site
  for v in values do
    require (ports.any (·.id == v.id)) .unknownReference site v.id
  for p in ports do
    require (values.any (·.id == p.id)) .missingBinding site p.id

private def checkBody (b : Body) (inputRoles : List PortRole) (initials : List Port) :
    Except Diagnostic Unit := do
  let sourcePorts := b.program.inputs ++ b.program.assignments.map Assignment.output
  checkPorts (sourcePorts ++ initials) "source"
  checkPorts (b.observations.map Observation.port) "observations"
  checkUnique ((sourcePorts ++ initials ++ b.observations.map Observation.port).map Port.id)
    .duplicateId "interface"
  for p in b.program.inputs do checkRole p inputRoles
  for a in b.program.assignments do
    checkRole a.output [.output]
    checkExpr (sourcePorts.map Port.name) a.output.id a.rhs
  checkValues (b.program.inputs.filter (·.role == .parameter)) b.parameters "parameters"
  for o in b.observations do
    checkRole o.port [.output]
    require (sourcePorts.any (·.id == o.sourceId)) .unknownReference o.port.id o.sourceId

private def checkEvolution (b : Body) (e : Evolution) : Except Diagnostic Unit := do
  require (!e.axis.id.isEmpty) .emptyId "axis" e.axis.name
  require (!e.axis.name.isEmpty) .emptyName "axis" e.axis.id
  require (e.evolveAlong == e.axis.id) .wrongAxis "evolveAlong" e.evolveAlong
  for p in e.initialPorts do checkRole p [.initial]
  checkValues e.initialPorts e.initialValues "initialValues"
  checkUnique (e.states.map Dynamics.StateBinding.stateId) .duplicateBinding "states"
  checkUnique (e.states.map Dynamics.StateBinding.derivativeId) .duplicateBinding "derivatives"
  checkUnique (e.states.map Dynamics.StateBinding.initialId) .duplicateBinding "initials"
  for s in e.states do
    require (b.program.inputs.any (fun p => p.id == s.stateId && p.role == .state))
      .unknownReference "states" s.stateId
    require (b.program.assignments.any (·.output.id == s.derivativeId))
      .unknownReference s.stateId s.derivativeId
    require (e.initialPorts.any (·.id == s.initialId))
      .unknownReference s.stateId s.initialId
  for p in b.program.inputs.filter (·.role == .state) do
    require (e.states.any (·.stateId == p.id)) .missingBinding "states" p.id
  for p in e.initialPorts do
    require (e.states.any (·.initialId == p.id)) .missingBinding "initials" p.id

/-- Every declared driver port is a `.driver` input, declared once, and every
`.driver` input is declared, as a driver or as a driver's derivative. -/
private def checkDrivers (b : Body) (ds : List DriverBinding) : Except Diagnostic Unit := do
  checkUnique (DriverBinding.ports ds) .duplicateBinding "drivers"
  for id in DriverBinding.ports ds do
    require (b.program.inputs.any (fun p => p.id == id && p.role == .driver))
      .unknownReference "drivers" id
  for p in b.program.inputs.filter (·.role == .driver) do
    require ((DriverBinding.ports ds).contains p.id) .missingBinding "drivers" p.id

/-- Checks declaration shape only. Forward references and auxiliary cycles are
left to the scheduling pass. State feedback is never treated
as an auxiliary dependency cycle. Unsupported operations are not constructors of
NamedExpr; unsupported port roles fail explicitly here. -/
def Declaration.validate : Declaration → Except Diagnostic Unit
  | .polynomial b => checkBody b [.input, .parameter] []
  | .continuous b e => do
      checkBody b [.state, .parameter] e.initialPorts
      checkEvolution b e
  | .driven b e ds => do
      checkBody b [.state, .parameter, .driver] e.initialPorts
      checkEvolution b e
      checkDrivers b ds

/-- A declaration together with evidence of this metadata check, not a compiled
circuit or a proof of existence, uniqueness, or a model property. -/
structure Checked where
  source : Declaration
  accepted : source.validate = .ok ()

def Declaration.check (d : Declaration) : Except Diagnostic Checked :=
  match h : d.validate with
  | .error error => .error error
  | .ok () => .ok ⟨d, h⟩

/-- Successful checking preserves the original source exactly. -/
theorem Declaration.check_source (d : Declaration) (c : Checked)
    (h : d.check = .ok c) : c.source = d := by
  unfold check at h
  split at h
  · contradiction
  · cases h
    rfl

#print axioms Declaration.check_source
end Gimle.Asgard.Model
