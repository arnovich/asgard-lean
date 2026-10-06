import Gimle.Asgard.Streams.RealTrigCalculus

/-! Physical derivatives and continuity of finite mild Fourier terms. -/
namespace Gimle.Asgard.Streams.Mild

open Torus Real

theorem meanZero_embed {P : TrigPoly} (h : Torus.MeanZero P) : MeanZero (embed P) := by
  change algebraMap ℚ ExpPoly (P 0) = 0
  rw [h, map_zero]

theorem isEven_embed {P : TrigPoly} (h : Torus.IsEven P) : IsEven (embed P) := by
  intro k
  simp only [embed_apply, h k]

theorem sizeLE_embed {P : TrigPoly} {K : ℕ} (h : Torus.SizeLE K P) : SizeLE K (embed P) := by
  intro k hk
  apply h k
  rw [Finsupp.mem_support_iff] at hk ⊢
  intro hz; exact hk (by simp [hz])

/-- Real evaluation preserves finite support bounds. -/
theorem sizeLE_eval (ν : ℚ) (t : ℝ) {P : MildPoly} {K : ℕ} (h : SizeLE K P) :
    RealPoly.SizeLE K (eval ν t P) := fun k hk => h k (support_eval_subset ν t P hk)

theorem meanZero_eval (ν : ℚ) (t : ℝ) {P : MildPoly} (h : MeanZero P) :
    RealPoly.MeanZero (eval ν t P) := by
  change ExpPoly.eval ν t (P 0) = 0
  rw [h, map_zero]

theorem isEven_eval (ν : ℚ) (t : ℝ) {P : MildPoly} (h : IsEven P) :
    RealPoly.IsEven (eval ν t P) := by intro k; change ExpPoly.eval ν t (P (-k)) = ExpPoly.eval ν t (P k); rw [h k]

/-- The real Laplacian agrees with physical evaluation. -/
theorem eval_laplacian (ν : ℚ) (t : ℝ) (P : MildPoly) :
    eval ν t (laplacian P) = RealPoly.laplacian (eval ν t P) := by
  apply Finsupp.ext
  intro k
  simp [Algebra.smul_def]

/-- The exact inverse Laplacian, omitting the mean mode. -/
noncomputable def laplacianInv (P : MildPoly) : MildPoly :=
  Finsupp.onFinset P.support (fun k => if k = 0 then 0 else -(lam k : ℚ)⁻¹ • P k)
    (fun k h => Finsupp.mem_support_iff.mpr (fun hz => h (by simp [hz])))

@[simp] theorem laplacianInv_apply (P : MildPoly) (k : Wave) :
    laplacianInv P k = if k = 0 then 0 else -(lam k : ℚ)⁻¹ • P k := rfl

theorem eval_laplacianInv (ν : ℚ) (t : ℝ) (P : MildPoly) :
    eval ν t (laplacianInv P) = RealPoly.laplacianInv (eval ν t P) := by
  apply Finsupp.ext
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk, Algebra.smul_def, div_eq_mul_inv, mul_comm]

theorem support_laplacianInv_subset (P : MildPoly) : (laplacianInv P).support ⊆ P.support := by
  intro k hk
  rw [Finsupp.mem_support_iff] at hk ⊢
  intro hz; exact hk (by simp [hz])

theorem sizeLE_laplacianInv {P : MildPoly} {K : ℕ} (h : SizeLE K P) : SizeLE K (laplacianInv P) :=
  fun k hk => h k (support_laplacianInv_subset P hk)

/-- Physical differentiation commutes with the inverse spatial Laplacian. -/
theorem deriv_laplacianInv (ν : ℚ) (P : MildPoly) :
    deriv ν (laplacianInv P) = laplacianInv (deriv ν P) := by
  apply Finsupp.ext
  intro k
  simp only [deriv_apply, laplacianInv_apply]
  split_ifs <;> simp only [ExpPoly.deriv_zero, ExpPoly.deriv_smul]

/-- Read an evaluated finite sum over a support independent of physical time. -/
theorem sum_eval_eq (ν : ℚ) (t : ℝ) (P : MildPoly) (f : Wave → ℝ → ℝ)
    (hf : ∀ k, f k 0 = 0) :
    ∑ k ∈ (eval ν t P).support, f k (eval ν t P k) =
      ∑ k ∈ P.support, f k (ExpPoly.eval ν t (P k)) := by
  apply Finset.sum_subset (support_eval_subset ν t P)
  intro k _ hk
  rw [Finsupp.notMem_support_iff] at hk
  simpa only [eval_apply] using (congrArg (f k) hk).trans (hf k)

/-- Every fixed spatial linear Fourier functional is physically differentiable. -/
theorem hasDerivAt_eval_sum (ν : ℚ) (P : MildPoly) (c : Wave → ℝ) (t : ℝ) :
    HasDerivAt (fun t => ∑ k ∈ (eval ν t P).support, eval ν t P k * c k)
      (∑ k ∈ (eval ν t (deriv ν P)).support, eval ν t (deriv ν P) k * c k) t := by
  have hs : (deriv ν P).support ⊆ P.support := Finsupp.support_mapRange
  have h := HasDerivAt.fun_sum (u := P.support)
    (fun k _ => (ExpPoly.hasDerivAt ν (P k) t).mul_const (c k))
  have he (s : ℝ) := sum_eval_eq ν s P (fun k a => a * c k) (fun _ => by simp)
  simp_rw [he]
  have hd := sum_eval_eq ν t (deriv ν P) (fun k a => a * c k) (fun _ => by simp)
  rw [hd, Finset.sum_subset hs]
  · exact h
  · intro k _ hk
    have hz := Finsupp.notMem_support_iff.mp hk
    simp only [hz, map_zero, zero_mul]

/-- Every finite spatial Fourier functional with continuous weights is jointly continuous. -/
theorem continuous_eval_sum (ν : ℚ) (P : MildPoly) (c : Wave → (ℝ × ℝ) → ℝ)
    (hc : ∀ k, Continuous (c k)) :
    Continuous (fun z : ℝ × (ℝ × ℝ) =>
      ∑ k ∈ (eval ν z.1 P).support, eval ν z.1 P k * c k z.2) := by
  have he (z : ℝ × (ℝ × ℝ)) := sum_eval_eq ν z.1 P
    (fun k a => a * c k z.2) (fun _ => by simp)
  simp_rw [he]
  exact continuous_finsetSum _ (fun k _ =>
    ((ExpPoly.continuous_eval ν (P k)).comp continuous_fst).mul ((hc k).comp continuous_snd))

/-- Time differentiation of the finite physical field. -/
theorem hasDerivAt_eval_field (ν : ℚ) (P : MildPoly) (t : ℝ) (x : ℝ × ℝ) :
    HasDerivAt (fun t => RealPoly.field (eval ν t P) x)
      (RealPoly.field (eval ν t (deriv ν P)) x) t :=
  hasDerivAt_eval_sum ν P (fun k => cos (phase k x)) t

theorem continuous_eval_field (ν : ℚ) (P : MildPoly) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => RealPoly.field (eval ν z.1 P) z.2) :=
  continuous_eval_sum ν P (fun k x => cos (phase k x)) (fun k => (Real.continuous_cos.comp (continuous_phase k)))

theorem continuous_eval_fieldD₁ (ν : ℚ) (P : MildPoly) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => RealPoly.fieldD₁ (eval ν z.1 P) z.2) := by
  have h := continuous_eval_sum ν P (fun k x => -(k.1 : ℝ) * sin (phase k x))
    (fun k => continuous_const.mul ((Real.continuous_sin.comp (continuous_phase k))))
  convert h using 1
  funext z
  unfold RealPoly.fieldD₁
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem continuous_eval_fieldD₂ (ν : ℚ) (P : MildPoly) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => RealPoly.fieldD₂ (eval ν z.1 P) z.2) := by
  have h := continuous_eval_sum ν P (fun k x => -(k.2 : ℝ) * sin (phase k x))
    (fun k => continuous_const.mul ((Real.continuous_sin.comp (continuous_phase k))))
  convert h using 1
  funext z
  unfold RealPoly.fieldD₂
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem continuous_eval_fieldD₁₁ (ν : ℚ) (P : MildPoly) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => RealPoly.fieldD₁₁ (eval ν z.1 P) z.2) := by
  have h := continuous_eval_sum ν P (fun k x => -((k.1 : ℝ) * k.1) * cos (phase k x))
    (fun k => continuous_const.mul ((Real.continuous_cos.comp (continuous_phase k))))
  convert h using 1
  funext z
  unfold RealPoly.fieldD₁₁
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem continuous_eval_fieldD₂₂ (ν : ℚ) (P : MildPoly) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => RealPoly.fieldD₂₂ (eval ν z.1 P) z.2) := by
  have h := continuous_eval_sum ν P (fun k x => -((k.2 : ℝ) * k.2) * cos (phase k x))
    (fun k => continuous_const.mul ((Real.continuous_cos.comp (continuous_phase k))))
  convert h using 1
  funext z
  unfold RealPoly.fieldD₂₂
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem continuous_eval_fieldD₁₂ (ν : ℚ) (P : MildPoly) :
    Continuous (fun z : ℝ × (ℝ × ℝ) => RealPoly.fieldD₁₂ (eval ν z.1 P) z.2) := by
  have h := continuous_eval_sum ν P (fun k x => -((k.1 : ℝ) * k.2) * cos (phase k x))
    (fun k => continuous_const.mul ((Real.continuous_cos.comp (continuous_phase k))))
  convert h using 1
  funext z
  unfold RealPoly.fieldD₁₂
  apply Finset.sum_congr rfl
  intro k _
  ring

#print axioms hasDerivAt_eval_field
#print axioms continuous_eval_field
end Gimle.Asgard.Streams.Mild
