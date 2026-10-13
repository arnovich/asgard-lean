import Gimle.Asgard.Compile.Normalization

/-! Conditional single-variable polynomial isolation. The selected coordinate is
moved to zero by an explicit permutation; the remaining coordinates keep the
order supplied by that permutation. Polynomial inverse witnesses are checked
under explicit hypotheses, never inferred from totalized real division. -/
namespace Gimle.Asgard.Isolation
open Polynomial Normalization

def semanticVersion : String := "asgard.polynomial-isolation/v1"

/-- A successful decomposition carries a kernel-checked identity for every
external input and every proposed value of the removed coordinate. -/
structure Decomposition (e : Expr (n + 1)) where
  coefficient : Expr n
  offset : Expr n
  correct : ∀ (u : Point n) (z : ℝ),
    e.eval (Fin.cons z u) = coefficient.eval u * z + offset.eval u

theorem Decomposition.offset_correct {n : Nat} {e : Expr (n + 1)}
    (d : Decomposition e) (u : Point n) : d.offset.eval u = e.eval (Fin.cons 0 u) := by
  simpa using (d.correct u 0).symm

theorem Decomposition.coefficient_correct {n : Nat} {e : Expr (n + 1)}
    (d : Decomposition e) (u : Point n) :
    d.coefficient.eval u = e.eval (Fin.cons 1 u) - e.eval (Fin.cons 0 u) := by
  rw [d.correct, d.correct]
  ring

/-- Conservative affine recognition. Products are accepted when at least one
recognized coefficient is syntactically zero after the supported simplification.
Failure reports unsupported structure, not unsatisfiability. -/
def decompose {n : Nat} : (e : Expr (n + 1)) → Option (Decomposition e)
  | .var i => Fin.cases
      (some ⟨.constant 1, .constant 0, by intros; simp [Expr.eval]⟩)
      (fun j => some ⟨.constant 0, .var j, by intros; simp [Expr.eval]⟩) i
  | .constant q => some ⟨.constant 0, .constant q, by intros; simp [Expr.eval]⟩
  | .add a b => do
      let da ← decompose a
      let db ← decompose b
      return ⟨add da.coefficient db.coefficient, add da.offset db.offset, by
        intro u z
        simp only [Expr.eval, add_correct]
        rw [da.correct, db.correct]
        ring⟩
  | .neg a => do
      let da ← decompose a
      return ⟨neg da.coefficient, neg da.offset, by
        intro u z
        simp only [Expr.eval, neg_correct]
        rw [da.correct]
        ring⟩
  | .mul a b => do
      let da ← decompose a
      let db ← decompose b
      if ha : da.coefficient = .constant 0 then
        return ⟨mul da.offset db.coefficient, mul da.offset db.offset, by
          intro u z
          simp only [Expr.eval, mul_correct]
          rw [da.correct, db.correct, ha]
          simp only [Expr.eval, Rat.cast_zero, zero_mul, zero_add]
          ring⟩
      else if hb : db.coefficient = .constant 0 then
        return ⟨mul da.coefficient db.offset, mul da.offset db.offset, by
          intro u z
          simp only [Expr.eval, mul_correct]
          rw [da.correct, db.correct, hb]
          simp only [Expr.eval, Rat.cast_zero, zero_mul, zero_add]
          ring⟩
      else none

structure Equation (n : Nat) where
  lhs : Source (n + 1)
  rhs : Source (n + 1)

def Equation.Satisfies (q : Equation n) (x : Point (n + 1)) : Prop :=
  q.lhs.eval x = q.rhs.eval x

/-- Select any coordinate, keeping all other coordinates in their original
relative order. Callers may instead supply another explicit permutation. -/
def select (i : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  (finSuccEquiv' i).trans (finSuccEquiv' 0).symm

@[simp] theorem select_focus (i : Fin (n + 1)) : select i i = 0 := by
  simp [select]

@[simp] theorem select_external (i : Fin (n + 1)) (j : Fin n) :
    select i (i.succAbove j) = j.succ := by
  simp [select]

/-- rho maps original coordinates to the explicitly chosen isolation order:
selected variable first, then the remaining external coordinates. -/
def reconstruct (rho : Equiv.Perm (Fin (n + 1))) (u : Point n) (z : ℝ) :
    Point (n + 1) := fun i => Fin.cons (α := fun _ => ℝ) z u (rho i)

@[simp] theorem reconstruct_focus (i : Fin (n + 1)) (u : Point n) (z : ℝ) :
    reconstruct (select i) u z i = z := by simp [reconstruct]

@[simp] theorem reconstruct_external (i : Fin (n + 1)) (j : Fin n)
    (u : Point n) (z : ℝ) : reconstruct (select i) u z (i.succAbove j) = u j := by
  simp [reconstruct]

@[simp] theorem reconstruct_select_zero (u : Point n) (z : ℝ) :
    reconstruct (select 0) u z = Fin.cons z u := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simpa using reconstruct_external (0 : Fin (n + 1)) j u z

def Equation.residual (q : Equation n) (rho : Equiv.Perm (Fin (n + 1))) : Expr (n + 1) :=
  simplify (substitute (fun i => .var (rho i)) (.add q.lhs.normalize (.neg q.rhs.normalize)))

theorem Equation.residual_correct (q : Equation n) (rho : Equiv.Perm (Fin (n + 1)))
    (u : Point n) (z : ℝ) :
    (q.residual rho).eval (Fin.cons z u) =
      q.lhs.eval (reconstruct rho u z) - q.rhs.eval (reconstruct rho u z) := by
  simp only [residual, simplify_correct, substitute_correct, Expr.eval,
    Source.normalize_correct, sub_eq_add_neg]
  rfl

abbrev Prepared (q : Equation n) (rho : Equiv.Perm (Fin (n + 1))) :=
  Decomposition (q.residual rho)

def Equation.prepare (q : Equation n) (rho : Equiv.Perm (Fin (n + 1))) :
    Option (Prepared q rho) := decompose (q.residual rho)

def Decomposition.solution {n : Nat} {e : Expr (n + 1)} (d : Decomposition e) (inverse : Expr n) : Expr n :=
  neg (mul inverse d.offset)

@[simp] theorem Decomposition.solution_correct {n : Nat} {e : Expr (n + 1)} (d : Decomposition e) (inverse : Expr n)
    (u : Point n) : (d.solution inverse).eval u = -(inverse.eval u * d.offset.eval u) := by
  simp [solution]

theorem Decomposition.inverse_nonzero {n : Nat} {e : Expr (n + 1)} (d : Decomposition e) (inverse : Expr n)
    (u : Point n) (valid : d.coefficient.eval u * inverse.eval u = 1) :
    d.coefficient.eval u ≠ 0 := by
  intro zero
  simp [zero] at valid

/-- Equivalence retains the original domain/initial/boundary predicate on the
full reconstructed valuation. Existence requires that predicate at the solution;
this theorem does not assume or discharge it. -/
theorem Prepared.solution_iff {q : Equation n} {rho : Equiv.Perm (Fin (n + 1))}
    (d : Prepared q rho) (inverse : Expr n) (u : Point n)
    (valid : d.coefficient.eval u * inverse.eval u = 1)
    (constraint : Point (n + 1) → Prop) (z : ℝ) :
    (q.Satisfies (reconstruct rho u z) ∧ constraint (reconstruct rho u z)) ↔
      z = (d.solution inverse).compile.run u 0 ∧
        constraint (reconstruct rho u ((d.solution inverse).compile.run u 0)) := by
  have residual := d.correct u z
  rw [Equation.residual_correct] at residual
  have eq : q.Satisfies (reconstruct rho u z) ↔ z = (d.solution inverse).eval u := by
    rw [Equation.Satisfies, ← sub_eq_zero, residual, Decomposition.solution_correct]
    have solution_eq : d.coefficient.eval u * (-(inverse.eval u * d.offset.eval u)) +
        d.offset.eval u = 0 := by
      calc
        _ = -(d.coefficient.eval u * inverse.eval u) * d.offset.eval u + d.offset.eval u := by ring
        _ = 0 := by rw [valid]; ring
    constructor
    · intro h
      apply mul_left_cancel₀ (d.inverse_nonzero inverse u valid)
      linarith [solution_eq]
    · intro h
      rw [h]
      exact solution_eq
  simp only [Expr.compile_correct]
  rw [eq]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, h⟩

/-- Pointwise elimination retains constraints on the entire valuation family,
including equations at an initial point or multiple boundary points. No
differentiation, integration or ODE-solving theorem is asserted here. -/
theorem Prepared.family_iff {q : Equation n} {rho : Equiv.Perm (Fin (n + 1))}
    (d : Prepared q rho) (inverse : Expr n) {T : Type}
    (u : T → Point n) (valid : ∀ t, d.coefficient.eval (u t) * inverse.eval (u t) = 1)
    (constraint : (T → Point (n + 1)) → Prop) (z : T → ℝ) :
    ((∀ t, q.Satisfies (reconstruct rho (u t) (z t))) ∧
      constraint (fun t => reconstruct rho (u t) (z t))) ↔
    z = (fun t => (d.solution inverse).compile.run (u t) 0) ∧
      constraint (fun t => reconstruct rho (u t) ((d.solution inverse).compile.run (u t) 0)) := by
  have eq : (∀ t, q.Satisfies (reconstruct rho (u t) (z t))) ↔
      z = (fun t => (d.solution inverse).compile.run (u t) 0) := by
    constructor
    · intro h
      funext t
      exact ((d.solution_iff inverse (u t) (valid t) (fun _ => True) (z t)).mp
        ⟨h t, trivial⟩).1
    · intro h
      subst z
      intro t
      exact ((d.solution_iff inverse (u t) (valid t) (fun _ => True) _).mpr
        ⟨rfl, trivial⟩).1
  rw [eq]
  constructor <;> rintro ⟨rfl, h⟩ <;> exact ⟨rfl, h⟩

#print axioms Decomposition.inverse_nonzero
#print axioms Prepared.solution_iff
#print axioms Prepared.family_iff
end Gimle.Asgard.Isolation
