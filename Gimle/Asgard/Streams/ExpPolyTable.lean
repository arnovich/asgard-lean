import Gimle.Asgard.Streams.ExpPoly

/-! Computable lists for exact exponential polynomials.

Tables may contain repeated entries. Their meaning is the exact sum, so
normalization combines coefficients without changing the represented term.
-/
namespace Gimle.Asgard.Streams.ExpPoly

open Polynomial

/-- A sparse rational polynomial, represented by degree/coefficient entries. -/
abbrev PolyTable := List (ℕ × ℚ)

namespace PolyTable

noncomputable def toPoly (l : PolyTable) : ℚ[X] :=
  (l.map fun e => monomial e.1 e.2).sum

@[simp] theorem toPoly_nil : toPoly [] = 0 := rfl

@[simp] theorem toPoly_cons (e : ℕ × ℚ) (l : PolyTable) :
    toPoly (e :: l) = monomial e.1 e.2 + toPoly l := by simp [toPoly]

/-- The finite integration-by-parts inverse on one monomial. -/
def inverseMonomial (c : ℚ) : ℕ → ℚ → PolyTable
  | 0, a => [(0, a / c)]
  | n + 1, a => (n + 1, a / c) :: inverseMonomial c n (-(a / c) * (n + 1))

/-- The computable inverse solves the polynomial differential equation exactly. -/
theorem inverseMonomial_spec (c : ℚ) (hc : c ≠ 0) (n : ℕ) (a : ℚ) :
    c • toPoly (inverseMonomial c n a) + (toPoly (inverseMonomial c n a)).derivative =
      monomial n a := by
  induction n generalizing a with
  | zero =>
      simp only [inverseMonomial, toPoly_cons, toPoly_nil, add_zero,
        Polynomial.monomial_zero_left, Polynomial.derivative_C,
        Polynomial.smul_C, smul_eq_mul]
      congr 1
      field_simp
  | succ n ih =>
      simp only [inverseMonomial, toPoly_cons, smul_add, Polynomial.derivative_add,
        Polynomial.derivative_monomial_succ]
      have h := ih (-(a / c) * (n + 1))
      calc
        _ = c • monomial (n + 1) (a / c) +
            monomial n ((a / c) * (n + 1)) +
            (c • toPoly (inverseMonomial c n (-(a / c) * (n + 1))) +
              (toPoly (inverseMonomial c n (-(a / c) * (n + 1)))).derivative) := by abel
        _ = _ := by
          rw [h, neg_mul, map_neg, add_neg_cancel_right]
          rw [Polynomial.smul_monomial, smul_eq_mul]
          congr 1
          field_simp

theorem toPoly_inverseMonomial (c : ℚ) (hc : c ≠ 0) (n : ℕ) (a : ℚ) :
    toPoly (inverseMonomial c n a) = inverse c (monomial n a) :=
  inverse_unique c hc _ _ (inverseMonomial_spec c hc n a)

/-- The constant coefficient, computed directly from a sparse polynomial. -/
def constant (l : PolyTable) : ℚ := (l.map fun e => if e.1 = 0 then e.2 else 0).sum

theorem constant_eq (l : PolyTable) : constant l = (toPoly l).eval 0 := by
  induction l with
  | nil => simp [constant]
  | cons e l ih =>
      simp only [constant, List.map_cons, List.sum_cons]
      rw [← constant, ih, toPoly_cons, Polynomial.eval_add, Polynomial.eval_monomial]
      by_cases h : e.1 = 0 <;> simp [h]

end PolyTable

/-- Sparse entries ((heat rate, polynomial degree), rational coefficient). -/
abbrev Table := List ((ℕ × ℕ) × ℚ)

namespace Table

/-- The exact term denoted by one sparse entry. -/
noncomputable def term (e : (ℕ × ℕ) × ℚ) : ExpPoly :=
  AddMonoidAlgebra.single e.1.1 (monomial e.1.2 e.2)

noncomputable def toExp (l : Table) : ExpPoly := (l.map term).sum

@[simp] theorem toExp_nil : toExp [] = 0 := rfl
@[simp] theorem toExp_cons (e : (ℕ × ℕ) × ℚ) (l : Table) :
    toExp (e :: l) = term e + toExp l := by simp [toExp]

theorem toExp_append (l m : Table) : toExp (l ++ m) = toExp l + toExp m := by
  simp [toExp]

/-- Read the exact coefficient, summing any repeated entries. -/
def coeff (k n : ℕ) : Table → ℚ
  | [] => 0
  | e :: l => (if e.1 = (k, n) then e.2 else 0) + coeff k n l

/-- Combine an entry with the first equal index, or append it. -/
def insert (index : ℕ × ℕ) (a : ℚ) : Table → Table
  | [] => [(index, a)]
  | e :: l => if e.1 = index then (index, e.2 + a) :: l else e :: insert index a l

theorem toExp_insert (index : ℕ × ℕ) (a : ℚ) (l : Table) :
    toExp (insert index a l) = term (index, a) + toExp l := by
  induction l with
  | nil => simp [insert]
  | cons e l ih =>
      simp only [insert]
      split_ifs with h
      · rw [toExp_cons, toExp_cons, ← h]
        simp only [term, map_add, AddMonoidAlgebra.single_add]
        abel
      · rw [toExp_cons, ih, toExp_cons]
        abel

private theorem toExp_filter_nonzero (l : Table) :
    toExp (l.filter fun e => e.2 != 0) = toExp l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      by_cases h : e.2 = 0 <;> simp [h, ih, term]

/-- Merge repeated indices and discard exact zero coefficients. -/
def normalize (l : Table) : Table :=
  (l.foldr (fun e acc => insert e.1 e.2 acc) []).filter fun e => e.2 != 0

theorem toExp_normalize (l : Table) : toExp (normalize l) = toExp l := by
  unfold normalize
  rw [toExp_filter_nonzero]
  induction l with
  | nil => rfl
  | cons e l ih => rw [List.foldr_cons, toExp_insert, ih, toExp_cons]

def smul (a : ℚ) (l : Table) : Table := l.map fun e => (e.1, a * e.2)

theorem toExp_smul (a : ℚ) (l : Table) : toExp (smul a l) = a • toExp l := by
  induction l with
  | nil => simp [smul]
  | cons e l ih =>
      rw [smul, List.map_cons, toExp_cons, ← smul, ih, toExp_cons, smul_add]
      congr 1
      simp [term, AddMonoidAlgebra.smul_single, Polynomial.smul_monomial, smul_eq_mul]

/-- Place every polynomial entry at one exponential rate. -/
def atRate (k : ℕ) (l : PolyTable) : Table := l.map fun e => ((k, e.1), e.2)

theorem toExp_atRate (k : ℕ) (l : PolyTable) :
    toExp (atRate k l) = AddMonoidAlgebra.single k l.toPoly := by
  induction l with
  | nil => simp [atRate]
  | cons e l ih =>
      rw [atRate, List.map_cons, toExp_cons, ← atRate, ih, PolyTable.toPoly_cons,
        AddMonoidAlgebra.single_add]
      rfl

/-- Integrate one monomial against the target heat kernel using exact rationals. -/
def duhamelEntry (ν : ℚ) (μ : ℕ) (e : (ℕ × ℕ) × ℚ) : Table :=
  let c : ℚ := ν * ((μ : ℚ) - (e.1.1 : ℚ))
  if c = 0 then [((e.1.1, e.1.2 + 1), e.2 / (e.1.2 + 1))]
  else
    let q := PolyTable.inverseMonomial c e.1.2 e.2
    atRate e.1.1 q ++ [((μ, 0), -q.constant)]

theorem toExp_duhamelEntry (ν : ℚ) (μ : ℕ) (e : (ℕ × ℕ) × ℚ) :
    toExp (duhamelEntry ν μ e) = ExpPoly.duhamel ν μ (term e) := by
  rw [term, ExpPoly.duhamel_single]
  unfold duhamelEntry duhamelTerm
  dsimp only
  split_ifs with hc
  · simp [term]
  · rw [toExp_append, toExp_atRate, PolyTable.constant_eq,
      PolyTable.toPoly_inverseMonomial _ hc]
    simp [term, sub_eq_add_neg]

/-- Exact Duhamel integration of a sparse exponential polynomial. -/
def duhamel (ν : ℚ) (μ : ℕ) (l : Table) : Table :=
  normalize (l.flatMap (duhamelEntry ν μ))

theorem toExp_duhamel (ν : ℚ) (μ : ℕ) (l : Table) :
    toExp (duhamel ν μ l) = ExpPoly.duhamel ν μ (toExp l) := by
  unfold duhamel
  rw [toExp_normalize]
  induction l with
  | nil => simp
  | cons e l ih =>
      rw [List.flatMap_cons, toExp_append, toExp_duhamelEntry, ih,
        toExp_cons, ExpPoly.duhamel_add]

/-- Convolution of polynomial degrees and heat rates. -/
def mul (l m : Table) : Table := normalize (l.flatMap fun e =>
  m.map fun f => ((e.1.1 + f.1.1, e.1.2 + f.1.2), e.2 * f.2))

private theorem toExp_mul_entry (e : (ℕ × ℕ) × ℚ) (m : Table) :
    toExp (m.map fun f => ((e.1.1 + f.1.1, e.1.2 + f.1.2), e.2 * f.2)) =
      term e * toExp m := by
  induction m with
  | nil => simp
  | cons f m ih =>
      rw [List.map_cons, toExp_cons, ih, toExp_cons, mul_add]
      congr 1
      simp [term, AddMonoidAlgebra.single_mul_single, Polynomial.monomial_mul_monomial]

theorem toExp_mul (l m : Table) : toExp (mul l m) = toExp l * toExp m := by
  unfold mul
  rw [toExp_normalize]
  induction l with
  | nil => simp
  | cons e l ih =>
      rw [List.flatMap_cons, toExp_append, toExp_mul_entry, ih, toExp_cons, add_mul]

/-- Multiplication by a heat exponential shifts only the rate. -/
def heat (rate : ℕ) (l : Table) : Table :=
  l.map fun e => ((rate + e.1.1, e.1.2), e.2)

theorem toExp_heat (rate : ℕ) (l : Table) :
    toExp (heat rate l) = AddMonoidAlgebra.single rate 1 * toExp l := by
  induction l with
  | nil => simp [heat]
  | cons e l ih =>
      rw [heat, List.map_cons, toExp_cons, ← heat, ih, toExp_cons, mul_add]
      congr 1
      simp [term, AddMonoidAlgebra.single_mul_single]

/-- Table coefficient reads coincide with the exact carrier's coefficients. -/
theorem toExp_coeff (l : Table) (k n : ℕ) : ((toExp l).coeff k).coeff n = coeff k n l := by
  induction l with
  | nil => simp [coeff]
  | cons e l ih =>
      rcases e with ⟨⟨r, m⟩, a⟩
      by_cases hr : r = k <;> by_cases hm : m = n <;>
        simp_all [coeff, term, Polynomial.coeff_monomial, eq_comm]

end Table
end Gimle.Asgard.Streams.ExpPoly
