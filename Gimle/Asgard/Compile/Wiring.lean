import Gimle.Asgard.Semantics.Real

/-! Primitive wiring for finite ordered real contexts. No additional circuit
constructors or semantic axioms are introduced. -/
namespace Gimle.Asgard.Wiring

/-- Empty wiring is derived from the existing constant and discard primitives. -/
def empty : Circuit 0 0 := .compose (.const 0) .terminal

def identity : (n : Nat) → Circuit n n
  | 0 => empty
  | n + 1 => .parallel (identity n) .id

def discard : (n : Nat) → Circuit n 0
  | 0 => empty
  | n + 1 => .parallel (discard n) .terminal

@[simp] theorem identity_run (n : Nat) (x : Point n) : (identity n).run x = x := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      funext i
      simp only [identity, Circuit.run, ih, pointAppend, pointLeft, pointRight]
      split
      · rfl
      · congr 1
        apply Fin.ext
        simp
        omega

@[simp] theorem discard_run (n : Nat) (x : Point n) :
    (discard n).run x = (fun i => Fin.elim0 i) := by
  funext i
  exact Fin.elim0 i

/-- Append one coordinate, retaining every original input in its original order. -/
def copyWire : (n : Nat) → Fin n → Circuit n (n + 1)
  | 0, i => Fin.elim0 i
  | n + 1, i =>
      if h : i.val < n then
        .compose (.parallel (copyWire n ⟨i.val, h⟩) .id)
          (@Circuit.parallel n n 2 2 (identity n) .swap)
      else @Circuit.parallel n n 1 2 (identity n) .split

@[simp] theorem copyWire_run (n : Nat) (i : Fin n) (x : Point n) :
    (copyWire n i).run x = pointAppend x ![x i] := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      unfold copyWire
      split_ifs with h
      · simp only [Circuit.run, identity_run, ih]
        funext j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · norm_num [pointAppend, pointLeft, pointRight]
        · refine Fin.lastCases ?_ (fun j => ?_) j
          · norm_num [pointAppend, pointLeft, pointRight]
          · have hj : j.val < n := j.isLt
            simp [pointAppend, pointLeft, hj, Nat.lt_trans hj (Nat.lt_succ_self n)]
      · have hi : i = Fin.last n := Fin.ext (by simp; omega)
        subst i
        funext j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · norm_num [Circuit.run, pointAppend, pointLeft, pointRight]
          rfl
        · refine Fin.lastCases ?_ (fun j => ?_) j
          · norm_num [Circuit.run, pointAppend, pointLeft, pointRight]
          · have hj : j.val < n := j.isLt
            simp [Circuit.run, pointAppend, pointLeft, hj,
              Nat.lt_trans hj (Nat.lt_succ_self n)]

end Gimle.Asgard.Wiring
