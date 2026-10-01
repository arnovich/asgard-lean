import Gimle.Asgard.Streams.Majorant
import Gimle.Asgard.Streams.Grid

/-! # Windows: the inverse's low coefficients, and bounds on the window field

A certified truncation (`Tail.lean`) says the analytic field is within `ε` of
the window field `Σ_{α < N} a_α x^α` on a box. To bound the field itself one
needs the window's coefficients as rationals the kernel can check and a bound
on the window polynomial over the box. This module gives both, for any
stream:

* `coeff_inv_window`: the coefficients of `φ⁻¹` below `N` are the unique
  solution of the finite triangular identity `(φ · Q)_α = [α = 0]` for
  `α < N`, so a table `Q` computed outside Lean is *checked*, coefficient by
  coefficient, never trusted;
* `sum_window_eq_grid`: a sum over the window is a list sum over the grid of
  degree vectors, which computes;
* `abs_windowField_sub_le`: on the box `|xᵢ| ≤ rᵢ`,
  `|W(x) − a₀| ≤ Σ_{0 ≠ α < N} |a_α| ∏ rᵢ^αᵢ`, a sum of exact rationals;
* `windowField_rat`: at a rational point the window field is the cast of a
  rational list sum.

Everything is in the OGF reading, where the decoded coefficient is the
coefficient. -/
namespace Gimle.Asgard.Streams

open MvPowerSeries Lowering

variable {d : Nat}

/-- Strictly below the window bound in every coordinate. -/
def Below (N : Fin d → ℕ) (α : Index d) : Prop := ∀ i, α i < N i

theorem below_iff_mem_window (N : Fin d → ℕ) (α : Index d) : Below N α ↔ α ∈ window N :=
  (mem_window N α).symm

theorem below_of_le {N : Fin d → ℕ} {α β : Index d} (hβ : Below N β) (h : α ≤ β) :
    Below N α :=
  fun i => lt_of_le_of_lt (Finsupp.le_def.mp h i) (hβ i)

/-- On the antidiagonal of `α`, the second component is below `α` unless the
pair is `(0, α)`. -/
theorem snd_lt_iff_ne {α : Index d} {p : Index d × Index d}
    (hp : p ∈ Finset.antidiagonal α) : p.2 < α ↔ p ≠ (0, α) := by
  rw [Finset.mem_antidiagonal] at hp
  have le : p.2 ≤ α := hp ▸ le_add_self
  constructor
  · intro lt eq
    rw [eq] at lt
    exact lt_irrefl _ lt
  · intro ne
    refine lt_of_le_of_ne le fun eq => ne ?_
    have first : p.1 = 0 := by
      have := hp
      rw [eq] at this
      exact add_eq_right.mp this
    exact Prod.ext first eq

/-- **The inverse's window is checked, not trusted.** If `Q` satisfies the
finite identity `(φ · Q)_α = [α = 0]` for every `α` below `N`, then `Q` is
the window of `φ⁻¹`: by well-founded induction on the index through Mathlib's
`coeff_inv` recurrence, both are determined by the same triangular system. -/
theorem coeff_inv_window (φ : Stream d) (hc : constantCoeff φ ≠ 0) (N : Fin d → ℕ)
    (Q : Index d → ℚ)
    (identity : ∀ α, Below N α →
      ∑ p ∈ Finset.antidiagonal α, coeff p.1 φ * Q p.2 = if α = 0 then 1 else 0) :
    ∀ α, Below N α → coeff α φ⁻¹ = Q α := by
  intro α
  refine WellFounded.induction (wellFounded_lt (α := Index d))
    (C := fun α => Below N α → coeff α φ⁻¹ = Q α) α ?_
  intro α ih hα
  have id := identity α hα
  by_cases h0 : α = 0
  · subst h0
    rw [Finsupp.antidiagonal_zero, Finset.sum_singleton, if_pos rfl,
      coeff_zero_eq_constantCoeff_apply] at id
    rw [show coeff (0 : Index d) φ⁻¹ = (constantCoeff φ)⁻¹ from
      (congrFun coeff_zero_eq_constantCoeff φ⁻¹).trans (constantCoeff_inv φ)]
    exact (eq_inv_of_mul_eq_one_right id).symm
  rw [coeff_inv, if_neg h0]
  have mem : ((0 : Index d), α) ∈ Finset.antidiagonal α :=
    Finset.mem_antidiagonal.mpr (zero_add α)
  have filt : (Finset.antidiagonal α).filter (fun p => p.2 < α) =
      (Finset.antidiagonal α).erase (0, α) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hp, lt⟩
      exact ⟨(snd_lt_iff_ne hp).mp lt, hp⟩
    · rintro ⟨ne, hp⟩
      exact ⟨hp, (snd_lt_iff_ne hp).mpr ne⟩
  have ite_sum : ∀ g : Index d × Index d → ℚ,
      ∑ p ∈ Finset.antidiagonal α, (if p.2 < α then g p else 0) =
        ∑ p ∈ Finset.antidiagonal α, g p - g (0, α) := by
    intro g
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, filt, Finset.sum_erase_eq_sub mem]
  have same : ∑ p ∈ Finset.antidiagonal α, (if p.2 < α then coeff p.1 φ * coeff p.2 φ⁻¹ else 0) =
      ∑ p ∈ Finset.antidiagonal α, (if p.2 < α then coeff p.1 φ * Q p.2 else 0) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    split_ifs with lt
    · rw [ih p.2 lt (below_of_le hα (le_of_lt lt))]
    · rfl
  rw [same, ite_sum, if_neg h0] at *
  rw [id, zero_sub, coeff_zero_eq_constantCoeff_apply]
  field_simp

/-! ## Sums over the window as list sums over the grid -/

theorem toIndex_coe (α : Index d) : Degrees.toIndex (⇑α : Degrees d) = α :=
  Finsupp.equivFunOnFinite.symm_apply_apply α

/-- The window below `N` (every `Nᵢ > 0`) is the grid below `N − 1`. -/
theorem sum_window_eq_grid {M : Type*} [AddCommMonoid M] (N : Fin d → ℕ) (hN : ∀ i, 0 < N i)
    (f : Index d → M) :
    ∑ α ∈ window N, f α = ((grid d fun i => N i - 1).map fun k => f k.toIndex).sum := by
  rw [← List.sum_toFinset _ (grid_nodup _)]
  symm
  refine Finset.sum_nbij' Degrees.toIndex (fun α => ⇑α) ?_ ?_ ?_ ?_ ?_
  · intro k member
    have below := (mem_grid _ k).mp (List.mem_toFinset.mp member)
    rw [mem_window]
    intro i
    have := below i
    have := hN i
    simp only [Degrees.toIndex_apply]
    omega
  · intro α member
    rw [mem_window] at member
    rw [List.mem_toFinset, mem_grid]
    intro i
    have := member i
    have := hN i
    omega
  · intro k _
    funext i
    rfl
  · intro α _
    exact toIndex_coe α
  · intro k _
    rfl

/-! ## Bounding the window field on a box -/

/-- At a point of the box, a monomial is bounded by the radii's monomial. -/
theorem abs_monomial_le {b : Box d} {x : Fin d → ℝ} (hx : b.Mem x) (α : Index d) :
    |∏ i, x i ^ α i| ≤ ∏ i, ((b.radius i : ℚ) : ℝ) ^ α i := by
  rw [Finset.abs_prod]
  refine Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => ?_
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _

/-- **The window field stays within a rational sum of the constant term.** On
the box `|xᵢ| ≤ rᵢ`, `|W(x) − a₀| ≤ Σ_{0 ≠ α < N} |a_α| ∏ rᵢ^αᵢ`. -/
theorem abs_windowField_sub_le (N : Fin d → ℕ) (hN : ∀ i, 0 < N i) (a : Stream d) (b : Box d)
    {x : Fin d → ℝ} (hx : b.Mem x) :
    |windowField .ogf N a x - ((coeff 0 a : ℚ) : ℝ)| ≤
      ∑ α ∈ window N,
        (if α = 0 then 0 else |((coeff α a : ℚ) : ℝ)| * ∏ i, ((b.radius i : ℚ) : ℝ) ^ α i) := by
  have mem0 : (0 : Index d) ∈ window N := (mem_window N 0).mpr (by simpa using hN)
  have head : seriesTerm .ogf a x 0 = ((coeff 0 a : ℚ) : ℝ) := by
    simp only [seriesTerm, decode, Finsupp.coe_zero, Pi.zero_apply, pow_zero,
      Finset.prod_const_one, mul_one]
    rfl
  have split := Finset.add_sum_erase (window N) (seriesTerm .ogf a x) mem0
  unfold windowField
  rw [← split, head, add_sub_cancel_left]
  calc |∑ α ∈ (window N).erase 0, seriesTerm .ogf a x α|
      ≤ ∑ α ∈ (window N).erase 0, |seriesTerm .ogf a x α| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ α ∈ (window N).erase 0, |((coeff α a : ℚ) : ℝ)| * ∏ i, ((b.radius i : ℚ) : ℝ) ^ α i := by
        refine Finset.sum_le_sum fun α _ => ?_
        simp only [seriesTerm, decode, abs_mul]
        exact mul_le_mul_of_nonneg_left (abs_monomial_le hx α) (abs_nonneg _)
    _ = ∑ α ∈ window N,
          (if α = 0 then 0 else |((coeff α a : ℚ) : ℝ)| * ∏ i, ((b.radius i : ℚ) : ℝ) ^ α i) := by
        rw [← Finset.sum_erase (window N) (f := fun α =>
          if α = 0 then (0 : ℝ) else |((coeff α a : ℚ) : ℝ)| * ∏ i, ((b.radius i : ℚ) : ℝ) ^ α i)
          (if_pos rfl)]
        refine Finset.sum_congr rfl fun α hα => ?_
        rw [if_neg (Finset.ne_of_mem_erase hα)]

/-- At a rational point the window field is a rational sum, cast. -/
theorem windowField_rat (N : Fin d → ℕ) (a : Stream d) (p : Fin d → ℚ) :
    windowField .ogf N a (fun i => (p i : ℝ)) =
      ((∑ α ∈ window N, coeff α a * ∏ i, p i ^ α i : ℚ) : ℝ) := by
  unfold windowField
  push_cast
  rfl

end Gimle.Asgard.Streams
