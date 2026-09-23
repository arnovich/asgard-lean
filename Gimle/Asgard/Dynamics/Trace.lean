import Gimle.Asgard.Dynamics.Feedback

namespace Gimle.Asgard.Dynamics

/-- Explicit wire reassociation used on both sides of trace fusion. -/
def unassociate (a b c : Nat) : Gimle.Asgard.Circuit (a + (b + c)) ((a + b) + c) :=
  Polynomial.route (Fin.cast (Nat.add_assoc a b c))

def associate (a b c : Nat) : Gimle.Asgard.Circuit ((a + b) + c) (a + (b + c)) :=
  Polynomial.route (Fin.cast (Nat.add_assoc a b c).symm)

@[simp] theorem unassociate_run {a b c : Nat} (x : Point a) (y : Point b) (z : Point c) :
    (unassociate a b c).run (pointAppend x (pointAppend y z)) =
      pointAppend (pointAppend x y) z := by
  rw [unassociate, Polynomial.route_correct]
  funext i
  simp only [pointAppend, Fin.val_cast]
  split_ifs <;> try omega
  all_goals congr 1
  all_goals apply Fin.ext
  all_goals dsimp
  all_goals omega

@[simp] theorem associate_run {a b c : Nat} (x : Point a) (y : Point b) (z : Point c) :
    (associate a b c).run (pointAppend (pointAppend x y) z) =
      pointAppend x (pointAppend y z) := by
  rw [associate, Polynomial.route_correct]
  funext i
  simp only [pointAppend, Fin.val_cast]
  split_ifs <;> try omega
  all_goals congr 1
  all_goals apply Fin.ext
  all_goals dsimp
  all_goals omega

/-- Merge two existentially hidden groups in the same continuous relation.
This is reassociation of witnesses, not an unconditional integrator/stream law. -/
def fuse {a b k l : Nat} (body : Circuit ((a + k) + l) ((b + k) + l)) :
    Circuit a b :=
  .trace (k + l) (.compose (.lift (unassociate a k l))
    (.compose body (.lift (associate b k l))))

theorem nested_trace_fusion {a b k l : Nat}
    (body : Circuit ((a + k) + l) ((b + k) + l)) :
    Equivalent (.trace k (.trace l body)) (fuse body) := by
  intro time x y
  simp only [Circuit.Rel, fuse]
  constructor
  · rintro ⟨u, v, h⟩
    refine ⟨signalAppend u v, _, rfl, signalAppend (signalAppend y u) v, ?_, ?_⟩
    · have hi : (fun t => (unassociate a k l).run
          (signalAppend x (signalAppend u v) t)) = signalAppend (signalAppend x u) v := by
        funext t
        exact unassociate_run _ _ _
      rw [hi]
      exact h
    · funext t
      exact (associate_run _ _ _).symm
  · rintro ⟨uv, input, hi, output, h, ho⟩
    subst input
    refine ⟨signalLeft uv, signalRight uv, ?_⟩
    have hinput : (fun t => (unassociate a k l).run (signalAppend x uv t)) =
        signalAppend (signalAppend x (signalLeft uv)) (signalRight uv) := by
      rw [← signalAppend_parts uv]
      simp only [signalLeft_append, signalRight_append]
      funext t
      exact unassociate_run _ _ _
    rw [hinput] at h
    have hout : output = signalAppend (signalAppend y (signalLeft uv)) (signalRight uv) := by
      have hassoc : (fun t => (associate b k l).run (output t)) =
          signalAppend (signalLeft (signalLeft output))
            (signalAppend (signalRight (signalLeft output)) (signalRight output)) := by
        conv_lhs => rw [← signalAppend_parts output, ← signalAppend_parts (signalLeft output)]
        funext t
        exact associate_run _ _ _
      rw [hassoc] at ho
      have hy := congrArg signalLeft ho
      have huv := congrArg signalRight ho
      have hu := congrArg signalLeft huv
      have hv := congrArg signalRight huv
      simp only [signalLeft_append, signalRight_append] at hy hu hv
      rw [hy, hu, hv, signalAppend_parts, signalAppend_parts]
    rwa [hout] at h

#print axioms nested_trace_fusion

end Gimle.Asgard.Dynamics
