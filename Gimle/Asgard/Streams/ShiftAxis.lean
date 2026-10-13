import Gimle.Asgard.Streams.Causal

/-! The plain interaction-degree shift, independent of the coefficient carrier. -/
namespace Gimle.Asgard.Streams

/-- Shift coefficients forward, reading only the boundary's initial slice. -/
def shiftFrom {C : Type*} (a boundary : ℕ → C) : ℕ → C
  | 0 => boundary 0
  | n + 1 => a n

@[simp] theorem shiftFrom_zero {C : Type*} (a b : ℕ → C) : shiftFrom a b 0 = b 0 := rfl
@[simp] theorem shiftFrom_succ {C : Type*} (a b : ℕ → C) (n : ℕ) :
    shiftFrom a b (n + 1) = a n := rfl

/-- Causal integration in interaction degree is the unweighted shift. -/
def shiftAxis (C : Type*) : Causal.Axis (ℕ → C) where
  Agree k a b := ∀ n ≤ k, a n = b n
  agree_refl _ _ _ _ := rfl
  agree_symm h n hn := (h n hn).symm
  agree_trans h h' n hn := (h n hn).trans (h' n hn)
  agree_mono h h' n hn := h' n (hn.trans h)
  agree_eq h := funext fun n => h n n le_rfl
  derivative a n := a (n + 1)
  integral := shiftFrom
  derivative_integral _ _ := rfl
  integral_derivative a := funext fun n => by cases n <;> rfl
  integral_slice a b n hn := by rw [Nat.le_zero.mp hn]; rfl
  integral_agree h hb n hn := by
    cases n with
    | zero => exact hb 0 le_rfl
    | succ m => exact h m (by omega)
  glue f n := f n n
  glue_agree chain n m hm := (chain m n hm m le_rfl).symm

@[simp] theorem shiftAxis_agree_zero {C : Type*} (a b : ℕ → C) :
    (shiftAxis C).Agree 0 a b ↔ a 0 = b 0 := by
  constructor
  · intro h; exact h 0 le_rfl
  · intro h n hn; simpa [Nat.le_zero.mp hn] using h

end Gimle.Asgard.Streams
