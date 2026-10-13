import Gimle.Asgard.Dynamics.Circuit
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Global existence and forward-domain uniqueness for autonomous continuous
linear fields. These analytic results do not depend on circuit compilation. -/
namespace Gimle.Asgard.Dynamics.LinearAnalysis

/-- A rational matrix acts continuously by exact real row sums. -/
noncomputable def rationalOperator {n : Nat} (a : Fin n → Fin n → ℚ) :
    Point n →L[ℝ] Point n :=
  ContinuousLinearMap.pi (fun i => ∑ j, (a i j : ℝ) • ContinuousLinearMap.proj j)

@[simp] theorem rationalOperator_apply {n : Nat} (a : Fin n → Fin n → ℚ)
    (x : Point n) (i : Fin n) :
    rationalOperator a x i = ∑ j, (a i j : ℝ) * x j := by
  simp [rationalOperator]

/-- The operator exponential gives a trajectory for every real time. -/
noncomputable def solution {n : Nat} (L : Point n →L[ℝ] Point n)
    (start : ℝ) (initial : Point n) : Signal n :=
  fun t => NormedSpace.exp ((t - start) • L) initial

@[simp] theorem solution_initial {n : Nat} (L : Point n →L[ℝ] Point n)
    (start : ℝ) (initial : Point n) : solution L start initial start = initial := by
  simp [solution, NormedSpace.exp_zero]

/-- No diagonalization or eigenvalue hypothesis is needed. -/
theorem solution_hasDerivAt {n : Nat} (L : Point n →L[ℝ] Point n)
    (start : ℝ) (initial : Point n) (t : ℝ) :
    HasDerivAt (solution L start initial) (L (solution L start initial t)) t := by
  have h := (hasDerivAt_exp_smul_const' L (t - start)).scomp t
    ((hasDerivAt_id t).sub_const start)
  have applied := h.clm_apply (hasDerivAt_const t initial)
  convert! applied using 1
  simp [solution, mul_apply_eq_comp]

/-- A global linear solution satisfies the forward coordinate-derivative relation. -/
theorem exists_solution {n : Nat} (L : Point n →L[ℝ] Point n)
    (start : ℝ) (initial : Point n) :
    ∃ state : Signal n, state start = initial ∧
      ∀ t ∈ Set.Ici start, ∀ i,
        HasDerivWithinAt (fun t => state t i) (L (state t) i) (Set.Ici start) t := by
  refine ⟨solution L start initial, solution_initial L start initial, ?_⟩
  intro t _ i
  exact ((hasDerivAt_pi.mp (solution_hasDerivAt L start initial t)) i).hasDerivWithinAt

/-- Uniqueness is restricted to the forward half-line. Values before the initial
instant are not constrained by the within-domain derivative assumptions. -/
theorem unique_on {n : Nat} (L : Point n →L[ℝ] Point n) (start : ℝ)
    (x y : Signal n) (initial : x start = y start)
    (hx : ∀ t ∈ Set.Ici start, ∀ i,
      HasDerivWithinAt (fun t => x t i) (L (x t) i) (Set.Ici start) t)
    (hy : ∀ t ∈ Set.Ici start, ∀ i,
      HasDerivWithinAt (fun t => y t i) (L (y t) i) (Set.Ici start) t) :
    Set.EqOn x y (Set.Ici start) := by
  have hx' : ∀ t ∈ Set.Ici start,
      HasDerivWithinAt x (L (x t)) (Set.Ici start) t :=
    fun t ht => hasDerivWithinAt_pi.mpr (hx t ht)
  have hy' : ∀ t ∈ Set.Ici start,
      HasDerivWithinAt y (L (y t)) (Set.Ici start) t :=
    fun t ht => hasDerivWithinAt_pi.mpr (hy t ht)
  intro t ht
  have equal : Set.EqOn x y (Set.Icc start t) :=
    ODE_solution_unique (v := fun _ z => L z) (fun _ => L.lipschitz)
      (fun u hu => (hx' u hu.1).continuousWithinAt.mono (fun _ hv => hv.1))
      (fun u hu => (hx' u hu.1).mono (fun _ hv => le_trans hu.1 hv))
      (fun u hu => (hy' u hu.1).continuousWithinAt.mono (fun _ hv => hv.1))
      (fun u hu => (hy' u hu.1).mono (fun _ hv => le_trans hu.1 hv))
      initial
  exact equal ⟨ht, le_rfl⟩

#print axioms solution_hasDerivAt
#print axioms exists_solution
#print axioms unique_on

end Gimle.Asgard.Dynamics.LinearAnalysis
