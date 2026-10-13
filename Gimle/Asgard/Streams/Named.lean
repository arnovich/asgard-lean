import Gimle.Asgard.Streams.Laws

/-! Stable axis IDs and ordinary input IDs have separate namespaces. Resolution
retains declared order; display names never infer a mathematical role. -/
namespace Gimle.Asgard.Streams

structure Axis where
  id : String
  name : String
  deriving Repr, DecidableEq, BEq

structure Context where
  axes : List Axis
  inputs : List Polynomial.Port
  deriving Repr, DecidableEq

def Context.valid (c : Context) : Bool :=
  decide ((c.axes.map Axis.id).Nodup ∧ (c.axes.map Axis.name).Nodup) &&
    c.axes.all (fun a => !a.id.isEmpty && !a.name.isEmpty) && Polynomial.validPorts c.inputs

def Context.axis (c : Context) (id : String) : Option (Fin c.axes.length) :=
  if c.valid then (Polynomial.lookupIndex (c.axes.map Axis.id) id).map
    (Fin.cast (List.length_map ..)) else none

def Context.input (c : Context) (id : String) : Option (Fin c.inputs.length) :=
  if c.valid then (Polynomial.lookupIndex (c.inputs.map Polynomial.Port.id) id).map
    (Fin.cast (List.length_map ..)) else none

theorem Context.axis_sound (c : Context) (id : String) (i : Fin c.axes.length)
    (found : c.axis id = some i) : c.axes[i].id = id := by
  unfold axis at found
  split at found
  · cases h : Polynomial.lookupIndex (c.axes.map Axis.id) id with
    | none => simp [h] at found
    | some j =>
      simp [h] at found
      subst i
      simpa using Polynomial.lookupIndex_sound (c.axes.map Axis.id) id j h
  · simp at found

inductive NamedUnary where
  | derivative (axis : String)
  deriving Repr, DecidableEq

inductive NamedBinary where
  | add | product
  | integral (axis : String)
  | seriesCompose (axis : String)
  deriving Repr, DecidableEq

/-- Historical source spelling for formal substitution along the named axis. -/
def NamedBinary.convolution (axis : String) : NamedBinary := .seriesCompose axis

def NamedUnary.resolve {d : Nat} (axes : String → Option (Fin d)) : NamedUnary → Option (Unary d)
  | .derivative i => (axes i).map Unary.derivative

def NamedBinary.resolve {d : Nat} (axes : String → Option (Fin d)) : NamedBinary → Option (Binary d)
  | .add => some .add
  | .product => some .product
  | .integral i => (axes i).map Binary.integral
  | .seriesCompose i => (axes i).map Binary.seriesCompose

inductive NamedExpr where
  | input (id : String)
  | constant (q : ℚ)
  | axisVariable (axis : String)
  | unary (op : NamedUnary) (a : NamedExpr)
  | binary (op : NamedBinary) (a b : NamedExpr)
  deriving Repr, DecidableEq

def NamedExpr.resolve {basis : Basis} {d n : Nat} (axes : String → Option (Fin d))
    (inputs : String → Option (Expr basis d n)) : NamedExpr → Option (Expr basis d n)
  | .input i => inputs i
  | .constant q => some (.constant q)
  | .axisVariable i => (axes i).map Expr.axisVariable
  | .unary op a => do return .unary (← op.resolve axes) (← a.resolve axes inputs)
  | .binary op a b => do
    return .binary (← op.resolve axes) (← a.resolve axes inputs) (← b.resolve axes inputs)

/-- Independent named source meaning carries both value and strict domain.
`some` means all names resolved; the proposition still needs to be proved. -/
noncomputable def NamedExpr.meaning {d : Nat} (basis : Basis) (axes : String → Option (Fin d))
    (inputs : String → Option (Stream d × Prop)) : NamedExpr → Option (Stream d × Prop)
  | .input i => inputs i
  | .constant q => some (Gimle.Asgard.Streams.constant basis q, True)
  | .axisVariable i => (axes i).map (fun j => (Gimle.Asgard.Streams.axisVariable basis j, True))
  | .unary op a => do
    let op ← op.resolve axes
    let a ← a.meaning basis axes inputs
    return (op.value basis a.1, a.2)
  | .binary op a b => do
    let op ← op.resolve axes
    let a ← a.meaning basis axes inputs
    let b ← b.meaning basis axes inputs
    return (op.value basis a.1 b.1, (a.2 ∧ b.2) ∧ op.Domain basis a.1 b.1)

noncomputable def Expr.meaning {basis : Basis} {d n : Nat} (x : StreamPoint d n)
    (e : Expr basis d n) : Stream d × Prop := (e.value x, e.Defined x)

theorem NamedExpr.resolve_correct {basis : Basis} {d n : Nat} (e : NamedExpr)
    (axes : String → Option (Fin d)) (inputs : String → Option (Expr basis d n))
    (x : StreamPoint d n) :
    (e.resolve axes inputs).map (Expr.meaning x) =
      e.meaning basis axes (fun id => (inputs id).map (Expr.meaning x)) := by
  induction e with
  | input i => rfl
  | constant q => rfl
  | axisVariable i =>
    simp only [resolve, NamedExpr.meaning]
    cases axes i <;> rfl
  | unary op a ha =>
    simp only [resolve, NamedExpr.meaning]
    rw [← ha]
    cases op.resolve axes <;> cases a.resolve axes inputs <;> rfl
  | binary op a b ha hb =>
    simp only [resolve, NamedExpr.meaning]
    rw [← ha, ← hb]
    cases op.resolve axes <;> cases a.resolve axes inputs <;> cases b.resolve axes inputs <;> rfl

def Context.resolve (c : Context) (basis : Basis) (e : NamedExpr) :
    Option (Expr basis c.axes.length c.inputs.length) :=
  if c.valid then e.resolve c.axis (fun id => (c.input id).map Expr.input) else none

noncomputable def Context.meaning (c : Context) (basis : Basis) (e : NamedExpr)
    (x : StreamPoint c.axes.length c.inputs.length) : Option (Stream c.axes.length × Prop) :=
  if c.valid then e.meaning basis c.axis (fun id => (c.input id).map (fun i => (x i, True))) else none

theorem Context.resolve_correct (c : Context) (basis : Basis) (e : NamedExpr)
    (x : StreamPoint c.axes.length c.inputs.length) :
    (c.resolve basis e).map (Expr.meaning x) = c.meaning basis e x := by
  simp only [resolve, meaning]
  split
  · rw [NamedExpr.resolve_correct]
    simp only [Option.map_map]
    rfl
  · rfl

/-- A resolved source's domain and value are exactly the compiled behavior. -/
theorem Context.compiled_iff (c : Context) (basis : Basis) (e : NamedExpr)
    (resolved : Expr basis c.axes.length c.inputs.length) (accepted : c.resolve basis e = some resolved)
    (x : StreamPoint c.axes.length c.inputs.length) (y : StreamPoint c.axes.length 1) :
    resolved.compile.Rel x y ↔ ∃ value domain,
      c.meaning basis e x = some (value, domain) ∧ domain ∧ y = ![value] := by
  have h := c.resolve_correct basis e x
  rw [accepted] at h
  rw [← h, Expr.compile_rel]
  simp only [Option.map_some, Expr.meaning, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨hd, hy⟩
    exact ⟨_, _, ⟨rfl, rfl⟩, hd, hy⟩
  · rintro ⟨v, domain, ⟨rfl, rfl⟩, hd, hy⟩
    exact ⟨hd, hy⟩

#print axioms Context.axis_sound
#print axioms NamedExpr.resolve_correct
#print axioms Context.compiled_iff
end Gimle.Asgard.Streams
