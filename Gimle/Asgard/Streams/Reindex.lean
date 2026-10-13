import Gimle.Asgard.Streams.Core

namespace Gimle.Asgard.Streams

/-- p maps each old axis to its new position. Pull the new multi-index back
before reading an old coefficient; the direction is explicit. -/
noncomputable def pullIndex {d e : Nat} (p : Fin d ≃ Fin e) (n : Index e) : Index d :=
  Finsupp.equivFunOnFinite.symm (fun i => n (p i))

@[simp] theorem pullIndex_apply {d e : Nat} (p : Fin d ≃ Fin e) (n : Index e) (i : Fin d) :
    pullIndex p n i = n (p i) := rfl

noncomputable def reindex {d e : Nat} (p : Fin d ≃ Fin e) (a : Stream d) : Stream e :=
  fun n => a (pullIndex p n)

theorem pullIndex_update {d e : Nat} (p : Fin d ≃ Fin e) (n : Index e)
    (axis : Fin d) (degree : Nat) :
    pullIndex p (n.update (p axis) degree) = (pullIndex p n).update axis degree := by
  ext i
  simp [pullIndex, Finsupp.update_apply, p.injective.eq_iff]

theorem reindex_derivative {d e : Nat} (p : Fin d ≃ Fin e) (basis : Basis)
    (axis : Fin d) (a : Stream d) :
    reindex p (derivative basis axis a) = derivative basis (p axis) (reindex p a) := by
  funext n
  cases basis <;> simp [derivative, reindex, pullIndex_update]

theorem reindex_integral {d e : Nat} (p : Fin d ≃ Fin e) (basis : Basis)
    (axis : Fin d) (a boundary : Stream d) :
    reindex p (integral basis axis a boundary) =
      integral basis (p axis) (reindex p a) (reindex p boundary) := by
  funext n
  cases basis <;> simp [integral, reindex, pullIndex_update]

/-- Window bounds must be permuted with the axes, using the inverse map. -/
theorem reindex_truncate {d e : Nat} (p : Fin d ≃ Fin e) (window : Fin d → Nat)
    (a : Stream d) :
    reindex p (truncate window a) = truncate (fun j => window (p.symm j)) (reindex p a) := by
  funext n
  have inside : (∀ i, pullIndex p n i < window i) ↔ ∀ j, n j < window (p.symm j) := by
    constructor
    · intro h j; simpa [pullIndex] using h (p.symm j)
    · intro h i; simpa [pullIndex] using h (p i)
  simp only [reindex, truncate, inside]

theorem reindex_inverse {d e : Nat} (p : Fin d ≃ Fin e) (a : Stream d) :
    reindex p.symm (reindex p a) = a := by
  funext n
  change a (pullIndex p (pullIndex p.symm n)) = a n
  apply congrArg a
  ext i
  simp [pullIndex]

#print axioms reindex_derivative
#print axioms reindex_integral
#print axioms reindex_truncate
#print axioms reindex_inverse
end Gimle.Asgard.Streams
