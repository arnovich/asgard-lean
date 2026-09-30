import Gimle.Asgard.Streams.Core

/-! Degree vectors and the grid below one.

A multi-index as a plain function `Fin d → ℕ`, so that it computes, its
finitely supported counterpart, and the list of every degree vector
coordinatewise at most a given one, in a fixed order. A sum over the
antidiagonal of an index is a sum over that grid. The lowering pass builds on
this; so does the majorant calculus, which must not depend on the lowering. -/

namespace Gimle.Asgard.Streams.Lowering

open Gimle.Asgard.Streams

/-- A multi-index as a plain function, so lowering computes. -/
abbrev Degrees (d : Nat) := Fin d → ℕ

/-- Degree vectors compare as lists, so equality reduces in the kernel; the
generic instance for functions on a finite type does not. -/
scoped instance (priority := high) Degrees.decEq {d : Nat} : DecidableEq (Degrees d) :=
  fun a b => decidable_of_iff (List.ofFn a = List.ofFn b) List.ofFn_inj

/-- The finitely supported index a degree vector names. -/
noncomputable def Degrees.toIndex {d : Nat} (degrees : Degrees d) : Index d :=
  Finsupp.equivFunOnFinite.symm degrees

@[simp] theorem Degrees.toIndex_apply {d : Nat} (degrees : Degrees d) (i : Fin d) :
    degrees.toIndex i = degrees i := rfl

theorem Degrees.toIndex_injective {d : Nat} : Function.Injective (@Degrees.toIndex d) :=
  Finsupp.equivFunOnFinite.symm.injective

/-! ### Splitting an index -/

/-- Every degree vector coordinatewise at most `k`, in a fixed order. -/
def grid : (d : Nat) → Degrees d → List (Degrees d)
  | 0, _ => [Fin.elim0]
  | d + 1, k => (List.range (k 0 + 1)).flatMap fun a =>
      (grid d (Fin.tail k)).map (Fin.cons a)

theorem mem_grid : {d : Nat} → (k a : Degrees d) → (a ∈ grid d k ↔ ∀ i, a i ≤ k i)
  | 0, k, a => by simp [grid]; funext i; exact Fin.elim0 i
  | d + 1, k, a => by
      simp only [grid, List.mem_flatMap, List.mem_range, List.mem_map, mem_grid]
      constructor
      · rintro ⟨head, below, tail, tail_below, rfl⟩ i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using Nat.lt_succ_iff.mp below
        · simpa [Fin.tail] using tail_below j
      · intro below
        refine ⟨a 0, Nat.lt_succ_of_le (below 0), Fin.tail a, fun j => below j.succ, ?_⟩
        exact Fin.cons_self_tail a

theorem grid_nodup : {d : Nat} → (k : Degrees d) → (grid d k).Nodup
  | 0, _ => by simp [grid]
  | d + 1, k => by
      simp only [grid]
      refine List.nodup_flatMap.mpr ⟨fun a _ => (grid_nodup (Fin.tail k)).map
        (fun x y same => by simpa using congrArg Fin.tail same), ?_⟩
      refine List.nodup_range.pairwise_of_forall_ne (fun a _ b _ different => ?_)
      rw [Function.onFun, List.disjoint_left]
      simp only [List.mem_map]
      rintro _ ⟨x, _, rfl⟩ ⟨y, _, same⟩
      exact different (by simpa using (congrFun same 0).symm)

/-- A sum over the antidiagonal of an index is a sum over the grid below it. -/
theorem sum_antidiagonal {d : Nat} (k : Degrees d) (f : Index d → Index d → ℚ) :
    ∑ p ∈ Finset.antidiagonal k.toIndex, f p.1 p.2 =
      ((grid d k).map fun a => f a.toIndex (k - a).toIndex).sum := by
  rw [← List.sum_toFinset _ (grid_nodup k)]
  symm
  refine Finset.sum_nbij' (fun a => (a.toIndex, (k - a).toIndex)) (fun p => ⇑p.1)
    ?_ ?_ ?_ ?_ ?_
  · intro a member
    have below := (mem_grid k a).mp (List.mem_toFinset.mp member)
    rw [Finset.mem_antidiagonal]
    ext i
    simp [Nat.add_sub_cancel' (below i)]
  · intro p member
    rw [Finset.mem_antidiagonal] at member
    rw [List.mem_toFinset, mem_grid]
    intro i
    have := congrArg (fun q => q i) member
    simp at this
    omega
  · intro a _
    rfl
  · intro p member
    rw [Finset.mem_antidiagonal] at member
    have second : (k - ⇑p.1) = ⇑p.2 := by
      funext i
      have := congrArg (fun q => q i) member
      simp at this
      simp
      omega
    ext i <;> simp [second]
  · intro a _
    rfl

end Gimle.Asgard.Streams.Lowering
