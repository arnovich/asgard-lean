import Gimle.Asgard.Dynamics.Circuit

namespace Gimle.Asgard.Dynamics

/-- Reorder [external, initial, state] to [external, state, initial]. -/
def prepare (d n : Nat) : Gimle.Asgard.Circuit ((d + n) + n) ((d + n) + n) :=
  Polynomial.route (Fin.addCases
    (Fin.addCases (fun i => Fin.castAdd n (Fin.castAdd n i)) (Fin.natAdd (d + n)))
    (fun i => Fin.castAdd n (Fin.natAdd d i)))

@[simp] theorem prepare_run {d n : Nat} (u : Point d) (ic x : Point n) :
    (prepare d n).run (pointAppend (pointAppend u ic) x) =
      pointAppend (pointAppend u x) ic := by
  rw [prepare, Polynomial.route_correct]
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simp only [Fin.addCases_left]
      simp [pointAppend, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right d n)]
    · intro i
      simp only [Fin.addCases_left, Fin.addCases_right]
      simp [pointAppend]
  · intro i
    simp only [Fin.addCases_right]
    simp [pointAppend]

/-- Every exposed state is the same wire fed back into the field. -/
def duplicate (n : Nat) : Gimle.Asgard.Circuit n (n + n) :=
  Polynomial.route (Fin.addCases id id)

@[simp] theorem duplicate_run {n : Nat} (x : Point n) :
    (duplicate n).run x = pointAppend x x := by
  rw [duplicate, Polynomial.route_correct]
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp only [Fin.addCases_left]
    simp [pointAppend]
  · intro i
    simp only [Fin.addCases_right]
    simp [pointAppend]

/-- Actual loop body: route inputs, evaluate the field, integrate with the
corresponding initial values, then expose and feed back each resulting state. -/
def feedbackBody {d n : Nat} (axis : String)
    (field : Gimle.Asgard.Circuit (d + n) n) : Circuit ((d + n) + n) (n + n) :=
  .compose (.lift (prepare d n))
    (.compose (.parallel (.lift field) (.lift (Wiring.identity n)))
      (.compose (.integrate axis n) (.lift (duplicate n))))

/-- Close all state feedback wires; external input order is [drivers, initial]. -/
def close {d n : Nat} (axis : String)
    (field : Gimle.Asgard.Circuit (d + n) n) : Circuit (d + n) n :=
  .trace n (feedbackBody axis field)

@[simp] theorem parallel_lift_rel {a b c d : Nat}
    (f : Gimle.Asgard.Circuit a b) (g : Gimle.Asgard.Circuit c d)
    (time : TimeDomain) (x : Signal (a + c)) (y : Signal (b + d)) :
    (Circuit.parallel (.lift f) (.lift g)).Rel time x y ↔
      y = signalAppend (fun t => f.run (signalLeft x t))
        (fun t => g.run (signalRight x t)) := by
  constructor
  · rintro ⟨h, k⟩
    rw [← h, ← k]
    exact (signalAppend_parts y).symm
  · intro h
    subst y
    simp [Circuit.Rel]

/-- Feedback compilation preserves both directions of the observable trajectory
relation. Hidden field, integrator and feedback wires introduce no new solutions. -/
theorem close_correct {d n : Nat} (axis : String)
    (field : Gimle.Asgard.Circuit (d + n) n) (time : TimeDomain)
    (drivers : Signal d) (initial : Point n) (state : Signal n) :
    (close axis field).Rel time (signalAppend drivers (fun _ => initial)) state ↔
      axis = time.axis ∧ state time.start = initial ∧
      ∀ t ∈ time.domain, ∀ i,
        HasDerivWithinAt (fun t => state t i)
          (field.run (pointAppend (drivers t) (state t)) i) time.domain t := by
  simp only [close, feedbackBody, Circuit.Rel]
  constructor
  · rintro ⟨feedback, routed, hr, bank, hb, integrated, hi, hout⟩
    subst routed
    have hr : (fun t => (prepare d n).run
        (signalAppend (signalAppend drivers (fun _ => initial)) feedback t)) =
        signalAppend (signalAppend drivers feedback) (fun _ => initial) := by
      funext t
      exact prepare_run _ _ _
    rw [hr] at hb
    simp only [signalLeft_append, signalRight_append, Wiring.identity_run] at hb
    have hbank : bank = signalAppend
        (fun t => field.run (signalAppend drivers feedback t)) (fun _ => initial) := by
      rw [← hb.1, ← hb.2, signalAppend_parts]
    subst bank
    have hs : state = integrated := by
      funext t
      have h := congrFun hout t
      change pointAppend (state t) (feedback t) = _ at h
      rw [duplicate_run] at h
      simpa only [pointLeft_pointAppend] using congrArg pointLeft h
    have hf : feedback = integrated := by
      funext t
      have h := congrFun hout t
      change pointAppend (state t) (feedback t) = _ at h
      rw [duplicate_run] at h
      simpa only [pointRight_pointAppend] using congrArg pointRight h
    subst feedback
    subst integrated
    simpa only [signalAppend, pointLeft_pointAppend, pointRight_pointAppend] using hi
  · intro h
    refine ⟨state, _, rfl,
      signalAppend (fun t => field.run (pointAppend (drivers t) (state t)))
        (fun _ => initial), ?_, state, ?_, ?_⟩
    · rw [show (fun t => (prepare d n).run
          (signalAppend (signalAppend drivers (fun _ => initial)) state t)) =
          signalAppend (signalAppend drivers state) (fun _ => initial) by
        funext t; exact prepare_run _ _ _]
      simp only [signalLeft_append, signalRight_append, Wiring.identity_run]
      exact ⟨rfl, trivial⟩
    · simpa only [signalAppend, pointLeft_pointAppend, pointRight_pointAppend] using h
    · funext t
      exact (duplicate_run (state t)).symm

#print axioms close_correct

end Gimle.Asgard.Dynamics
