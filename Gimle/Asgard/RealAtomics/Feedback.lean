import Gimle.Asgard.RealAtomics.Compiler
import Gimle.Asgard.Dynamics.Circuit

/-! Continuous feedback over a partial real vector field.

`Dynamics.close` closes a total polynomial field: its loop lifts a
`Gimle.Asgard.Circuit`, whose run is defined everywhere. A `RealAtomics` field
is partial, and a `Dynamics.Circuit` cannot lift its operational relation. This
module therefore states the same trace directly: the hidden feedback wire is
fed, with the drivers, through the field's own `Circuit.Rel` at every time of the
forward domain, and the resulting rates enter the unchanged
`Dynamics.Circuit.integrate` bank. Because the loop uses `Rel` rather than the
totalized `value`, `Defined` is part of the relation at every such time. The
field's single axis is the time of the continuous domain, so a generator reads
`t`. As with `Dynamics.close`, the trace asserts no existence or uniqueness. -/
namespace Gimle.Asgard.RealAtomics

/-- The axis point of a field evaluated at time `t`: the only axis is time. -/
def timeAxis (t : ℝ) : Point 1 := ![t]

/-- Partial-field feedback, with external input order [drivers, initial] as in
`Dynamics.close`. The feedback wire is existential; at every time of the forward
domain it and the drivers must be admitted by the field's operational relation,
and its rates are integrated by the ordinary `Dynamics` integrator bank. The
exposed state is the feedback wire itself. -/
def Circuit.CloseRel {d n : Nat} (axis : String) (field : Circuit 1 (d + n) n)
    (time : Dynamics.TimeDomain) (input : Dynamics.Signal (d + n))
    (state : Dynamics.Signal n) : Prop :=
  ∃ feedback rates : Dynamics.Signal n,
    (∀ t ∈ time.domain, field.Rel (timeAxis t)
      (pointAppend (Dynamics.signalLeft input t) (feedback t)) (rates t)) ∧
    (Dynamics.Circuit.integrate axis n).Rel time
      (Dynamics.signalAppend rates (Dynamics.signalRight input)) feedback ∧
    state = feedback

/-- Partial-field feedback preserves both directions of the classical initialized
solution relation, and the field's domain is part of it: every time of the
forward domain must be `Defined` along the state. The totalized `value` is only
the rate at such defined points. -/
theorem Circuit.close_correct {d n : Nat} (axis : String) (field : Circuit 1 (d + n) n)
    (time : Dynamics.TimeDomain) (drivers : Dynamics.Signal d) (initial : Point n)
    (state : Dynamics.Signal n) :
    field.CloseRel axis time (Dynamics.signalAppend drivers (fun _ => initial)) state ↔
      axis = time.axis ∧ state time.start = initial ∧
      ∀ t ∈ time.domain,
        field.Defined (timeAxis t) (pointAppend (drivers t) (state t)) ∧
        ∀ i, HasDerivWithinAt (fun t => state t i)
          (field.value (timeAxis t) (pointAppend (drivers t) (state t)) i) time.domain t := by
  simp only [CloseRel, Dynamics.Circuit.Rel, Dynamics.signalLeft_append,
    Dynamics.signalRight_append, Dynamics.signalAppend, pointLeft_pointAppend,
    pointRight_pointAppend, rel_iff]
  constructor
  · rintro ⟨feedback, rates, hf, ⟨haxis, hstart, hderiv⟩, rfl⟩
    refine ⟨haxis, hstart, fun t ht => ⟨(hf t ht).1, fun i => ?_⟩⟩
    rw [← (hf t ht).2]
    exact hderiv t ht i
  · rintro ⟨haxis, hstart, h⟩
    exact ⟨state, fun t => field.value (timeAxis t) (pointAppend (drivers t) (state t)),
      fun t ht => ⟨(h t ht).1, rfl⟩, ⟨haxis, hstart, fun t ht => (h t ht).2⟩, rfl⟩

/-- A vector field whose coordinates are independent source expressions over
the same inputs, compiled with `Expr.compile` and paired. -/
def vectorField {k m : Nat} : {n : Nat} → (Fin n → Expr k m) → Circuit k m n
  | 0, _ => .embed (Wiring.discard m)
  | _ + 1, e => (vectorField (fun i => e i.castSucc)).pair (e (Fin.last _)).compile

@[simp] theorem vectorField_value {k m n : Nat} (e : Fin n → Expr k m)
    (axes : Point k) (x : Point m) :
    (vectorField e).value axes x = fun i => (e i).value axes x := by
  induction n with
  | zero => funext i; exact i.elim0
  | succ n ih =>
      funext i
      simp only [vectorField, Circuit.pair_value, ih, Expr.compile_value]
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [pointAppend]
      · simp [pointAppend]

@[simp] theorem vectorField_defined {k m n : Nat} (e : Fin n → Expr k m)
    (axes : Point k) (x : Point m) :
    (vectorField e).Defined axes x ↔ ∀ i, (e i).Defined axes x := by
  induction n with
  | zero => simp [vectorField, Circuit.Defined]
  | succ n ih =>
      simp only [vectorField, Circuit.pair_defined, ih, Expr.compile_defined]
      exact ⟨fun h i => Fin.lastCases h.2 h.1 i, fun h => ⟨fun i => h _, h _⟩⟩

/-- The expression form of `Circuit.close_correct`: coordinate `i` of the state
has derivative `e i` wherever every coordinate expression is `Defined`, and the
relation requires that at every time of the forward domain. -/
theorem Expr.close_correct {d n : Nat} (axis : String) (e : Fin n → Expr 1 (d + n))
    (time : Dynamics.TimeDomain) (drivers : Dynamics.Signal d) (initial : Point n)
    (state : Dynamics.Signal n) :
    (vectorField e).CloseRel axis time (Dynamics.signalAppend drivers (fun _ => initial))
        state ↔
      axis = time.axis ∧ state time.start = initial ∧
      ∀ t ∈ time.domain,
        (∀ i, (e i).Defined (timeAxis t) (pointAppend (drivers t) (state t))) ∧
        ∀ i, HasDerivWithinAt (fun t => state t i)
          ((e i).value (timeAxis t) (pointAppend (drivers t) (state t))) time.domain t := by
  rw [Circuit.close_correct]
  simp only [vectorField_defined, vectorField_value]

#print axioms Circuit.close_correct
#print axioms vectorField_value
#print axioms vectorField_defined
#print axioms Expr.close_correct
end Gimle.Asgard.RealAtomics
