import Gimle.Asgard.Streams.ExpPoly
import Gimle.Asgard.Streams.ShiftAxis
import Gimle.Asgard.Streams.Torus

/-! Exact heat/Duhamel operations and the causal Wild expansion.

The axis counts nonlinear interactions. Its coefficients are functions of
physical time represented by exact exponential polynomials. No convergence
or classical-solution assertion belongs to this module.
-/
namespace Gimle.Asgard.Streams.Mild

open Torus Causal

/-- Finite Fourier polynomials with exact exponential-polynomial coefficients. -/
abbrev MildPoly := Wave →₀ ExpPoly

/-- A stream indexed by nonlinear interaction degree. -/
abbrev Stream := ℕ → MildPoly

/-- No zero mode: the mean over the torus vanishes. -/
def MeanZero (P : MildPoly) : Prop := P 0 = 0

/-- Coefficients even in `k`: with rational coefficients, the real-valued
(cosine) subspace. -/
def IsEven (P : MildPoly) : Prop := ∀ k, P (-k) = P k

theorem meanZero_add {P Q : MildPoly} (hP : MeanZero P) (hQ : MeanZero Q) : MeanZero (P + Q) := by
  unfold MeanZero at *
  simp [hP, hQ]

theorem meanZero_sub {P Q : MildPoly} (hP : MeanZero P) (hQ : MeanZero Q) : MeanZero (P - Q) := by
  unfold MeanZero at *
  simp [hP, hQ]

theorem meanZero_smul (c : ℚ) {P : MildPoly} (hP : MeanZero P) : MeanZero (c • P) := by
  unfold MeanZero at *
  simp [hP]

theorem meanZero_sum {ι : Type*} (s : Finset ι) {f : ι → MildPoly}
    (h : ∀ i ∈ s, MeanZero (f i)) : MeanZero (∑ i ∈ s, f i) := by
  unfold MeanZero at *
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero h

theorem isEven_add {P Q : MildPoly} (hP : IsEven P) (hQ : IsEven Q) : IsEven (P + Q) := by
  intro k
  simp [hP k, hQ k]

theorem isEven_sub {P Q : MildPoly} (hP : IsEven P) (hQ : IsEven Q) : IsEven (P - Q) := by
  intro k
  simp [hP k, hQ k]

theorem isEven_smul (c : ℚ) {P : MildPoly} (hP : IsEven P) : IsEven (c • P) := by
  intro k
  simp [hP k]

theorem isEven_sum {ι : Type*} (s : Finset ι) {f : ι → MildPoly}
    (h : ∀ i ∈ s, IsEven (f i)) : IsEven (∑ i ∈ s, f i) := by
  intro k
  rw [Finsupp.finsetSum_apply, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun i hi => h i hi k

/-- The natural heat index corresponding to the Fourier Laplacian. -/
def heatRate (k : Wave) : ℕ := (lam k).toNat

theorem lam_nonneg (k : Wave) : 0 ≤ lam k := by
  unfold lam
  positivity

@[simp] theorem heatRate_cast (k : Wave) : (heatRate k : ℤ) = lam k :=
  Int.toNat_of_nonneg (lam_nonneg k)

@[simp] theorem heatRate_neg (k : Wave) : heatRate (-k) = heatRate k := by
  simp [heatRate]

/-- Embed rational initial Fourier data as constant functions of physical time. -/
noncomputable def embed (P : TrigPoly) : MildPoly :=
  P.mapRange (algebraMap ℚ ExpPoly) (map_zero _)

@[simp] theorem embed_apply (P : TrigPoly) (k : Wave) :
    embed P k = algebraMap ℚ ExpPoly (P k) := rfl

/-- Real Fourier coefficients at a physical time, preserving rational linear operations. -/
noncomputable def eval (ν : ℚ) (t : ℝ) : MildPoly →ₗ[ℚ] (Wave →₀ ℝ) :=
  Finsupp.mapRange.linearMap (ExpPoly.eval ν t).toLinearMap

@[simp] theorem eval_apply (ν : ℚ) (t : ℝ) (P : MildPoly) (k : Wave) :
    eval ν t P k = ExpPoly.eval ν t (P k) := rfl

@[simp] theorem eval_embed (ν : ℚ) (t : ℝ) (P : TrigPoly) (k : Wave) :
    eval ν t (embed P) k = (P k : ℝ) := by simp

/-- Heat evolution multiplies each mode by its exact exponential. -/
noncomputable def heat (P : MildPoly) : MildPoly :=
  Finsupp.onFinset P.support
    (fun k => AddMonoidAlgebra.single (heatRate k) 1 * P k)
    (fun _ hk => Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hk))

@[simp] theorem heat_apply (P : MildPoly) (k : Wave) :
    heat P k = AddMonoidAlgebra.single (heatRate k) 1 * P k := rfl

/-- Integrate each mode against its heat kernel. -/
noncomputable def duhamel (ν : ℚ) (P : MildPoly) : MildPoly :=
  Finsupp.onFinset P.support (fun k => ExpPoly.duhamel ν (heatRate k) (P k))
    (fun k hk => Finsupp.mem_support_iff.mpr (fun hz => hk (by simp [hz])))

@[simp] theorem duhamel_apply (ν : ℚ) (P : MildPoly) (k : Wave) :
    duhamel ν P k = ExpPoly.duhamel ν (heatRate k) (P k) := rfl

/-- Physical time differentiation, not the interaction-degree shift. -/
noncomputable def deriv (ν : ℚ) (P : MildPoly) : MildPoly :=
  P.mapRange (ExpPoly.deriv ν) (ExpPoly.deriv_zero ν)

@[simp] theorem deriv_apply (ν : ℚ) (P : MildPoly) (k : Wave) :
    deriv ν P k = ExpPoly.deriv ν (P k) := rfl

/-- The spatial Laplacian multiplies each Fourier coefficient by -|k|². -/
noncomputable def laplacian (P : MildPoly) : MildPoly :=
  Finsupp.onFinset P.support (fun k => -(lam k : ℚ) • P k)
    (fun k hk => Finsupp.mem_support_iff.mpr (fun hz => hk (by simp [hz])))

@[simp] theorem laplacian_apply (P : MildPoly) (k : Wave) :
    laplacian P k = -(lam k : ℚ) • P k := rfl

/-- The bilinear transport term as a linear map in each argument: on single
modes, `transport (e_p) (e_q) = coupling p q · e_{p+q}`. -/
noncomputable def transportₗ : MildPoly →ₗ[ExpPoly] MildPoly →ₗ[ExpPoly] MildPoly :=
  Finsupp.lsum ExpPoly fun p => LinearMap.toSpanSingleton ExpPoly _
    (Finsupp.lsum ExpPoly fun q => LinearMap.toSpanSingleton ExpPoly _ (Finsupp.single (p + q) (algebraMap ℚ ExpPoly (coupling p q))))

/-- `transport P Q`: the bilinear form with the coupling `(p × q)/|p|²` on
`p + q = k`, the Fourier side of `u·∇Q` for `u = ∇⊥Δ⁻¹P`. -/
noncomputable def transport (P Q : MildPoly) : MildPoly := transportₗ P Q

theorem transport_eq_sum (P Q : MildPoly) :
    transport P Q = P.sum fun p a => a • Q.sum fun q b => b • Finsupp.single (p + q) (algebraMap ℚ ExpPoly (coupling p q)) := by
  simp only [transport, transportₗ, Finsupp.lsum_apply]
  rw [Finsupp.sum, Finsupp.sum]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, Finsupp.lsum_apply,
    Finsupp.sum, LinearMap.toSpanSingleton_apply]

theorem transport_add_left (P P' Q : MildPoly) :
    transport (P + P') Q = transport P Q + transport P' Q := by
  simp [transport, map_add]

theorem transport_add_right (P Q Q' : MildPoly) :
    transport P (Q + Q') = transport P Q + transport P Q' := by
  simp [transport, map_add]

theorem transport_zero_left (Q : MildPoly) : transport 0 Q = 0 := by simp [transport]

theorem transport_zero_right (P : MildPoly) : transport P 0 = 0 := by simp [transport]

/-- On single modes the transport is the coupling on the sum of the modes. -/
theorem transport_single_single (p q : Wave) (a b : ExpPoly) :
    transport (Finsupp.single p a) (Finsupp.single q b) =
      Finsupp.single (p + q) ((algebraMap ℚ ExpPoly (coupling p q)) * a * b) := by
  rw [transport_eq_sum, Finsupp.sum_single_index, Finsupp.sum_single_index]
  · rw [Finsupp.smul_single, Finsupp.smul_single, smul_eq_mul, smul_eq_mul]
    congr 1; ring
  · simp
  · simp

/-- The coefficient at `k`: a double sum over the supports with `p + q = k`. -/
theorem transport_apply (P Q : MildPoly) (k : Wave) :
    transport P Q k = ∑ p ∈ P.support, ∑ q ∈ Q.support,
      if p + q = k then (algebraMap ℚ ExpPoly (coupling p q)) * P p * Q q else 0 := by
  rw [transport_eq_sum, Finsupp.sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finsupp.sum, Finsupp.smul_apply, Finsupp.finsetSum_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The transport has no zero mode: `p × (−p) = 0`. -/
theorem meanZero_transport (P Q : MildPoly) : MeanZero (transport P Q) := by
  unfold MeanZero
  rw [transport_apply]
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
  split_ifs with h
  · have : q = -p := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h
    subst this
    simp
  · rfl

/-- Even factors give an even transport: negate both summation indices. -/
theorem isEven_transport {P Q : MildPoly} (hP : IsEven P) (hQ : IsEven Q) :
    IsEven (transport P Q) := by
  intro k
  rw [transport_apply, transport_apply]
  have memP : ∀ p, p ∈ P.support ↔ -p ∈ P.support := fun p => by
    simp [Finsupp.mem_support_iff, hP p]
  have memQ : ∀ q, q ∈ Q.support ↔ -q ∈ Q.support := fun q => by
    simp [Finsupp.mem_support_iff, hQ q]
  refine Finset.sum_nbij' (fun p => -p) (fun p => -p) (fun p hp => (memP p).mp hp)
    (fun p hp => (memP (-p)).mpr (by simpa using hp)) (fun _ _ => neg_neg _)
    (fun _ _ => neg_neg _) fun p _ => ?_
  refine Finset.sum_nbij' (fun q => -q) (fun q => -q) (fun q hq => (memQ q).mp hq)
    (fun q hq => (memQ (-q)).mpr (by simpa using hq)) (fun _ _ => neg_neg _)
    (fun _ _ => neg_neg _) fun q _ => ?_
  have cond : p + q = -k ↔ -p + -q = k := by
    rw [← neg_add, neg_eq_iff_eq_neg, eq_comm]
  simp only [cond, coupling_neg_neg, hP p, hQ q]

/-- Embedded physical initial data solve the homogeneous heat equation. -/
theorem deriv_heat_embed (ν : ℚ) (P : TrigPoly) :
    deriv ν (heat (embed P)) = ν • laplacian (heat (embed P)) := by
  apply Finsupp.ext
  intro k
  have hr : (heatRate k : ℚ) = (lam k : ℚ) := by exact_mod_cast heatRate_cast k
  simp only [deriv_apply, heat_apply, embed_apply, Finsupp.smul_apply, laplacian_apply]
  have he (a : ℚ) : algebraMap ℚ ExpPoly a =
      AddMonoidAlgebra.single 0 (Polynomial.C a) := rfl
  rw [he, AddMonoidAlgebra.single_mul_single]
  simp only [add_zero, one_mul, ExpPoly.deriv_single, Polynomial.derivative_C, zero_sub]
  ext j n
  simp [hr, Polynomial.smul_eq_C_mul, mul_assoc]

/-- Evaluation of degree zero really has the prescribed initial Fourier data. -/
@[simp] theorem eval_heat_embed_zero (ν : ℚ) (P : TrigPoly) (k : Wave) :
    eval ν 0 (heat (embed P)) k = (P k : ℝ) := by simp

/-- Every integrated forcing coefficient starts at zero physical time. -/
@[simp] theorem eval_duhamel_zero (ν : ℚ) (P : MildPoly) : eval ν 0 (duhamel ν P) = 0 := by
  apply Finsupp.ext
  intro k
  simp

@[simp] theorem heat_zero : heat 0 = 0 := by
  apply Finsupp.ext; intro k; simp

@[simp] theorem heat_single (k : Wave) (P : ExpPoly) :
    heat (Finsupp.single k P) = Finsupp.single k (AddMonoidAlgebra.single (heatRate k) 1 * P) := by
  apply Finsupp.ext
  intro j
  by_cases h : k = j <;> simp [h]

@[simp] theorem duhamel_zero (ν : ℚ) : duhamel ν 0 = 0 := by
  apply Finsupp.ext; intro k; simp

@[simp] theorem duhamel_single (ν : ℚ) (k : Wave) (P : ExpPoly) :
    duhamel ν (Finsupp.single k P) = Finsupp.single k (ExpPoly.duhamel ν (heatRate k) P) := by
  apply Finsupp.ext
  intro j
  by_cases h : k = j <;> simp [h]

/-! ## Linear operations and preserved subspaces -/

theorem heat_add (P Q : MildPoly) : heat (P + Q) = heat P + heat Q := by
  apply Finsupp.ext; intro k; simp [mul_add]

theorem duhamel_add (ν : ℚ) (P Q : MildPoly) :
    duhamel ν (P + Q) = duhamel ν P + duhamel ν Q := by
  apply Finsupp.ext; intro k; simp [ExpPoly.duhamel_add]

theorem duhamel_smul (ν a : ℚ) (P : MildPoly) :
    duhamel ν (a • P) = a • duhamel ν P := by
  apply Finsupp.ext; intro k; simp [ExpPoly.duhamel_smul]

theorem deriv_neg (ν : ℚ) (P : MildPoly) : deriv ν (-P) = -deriv ν P := by
  apply Finsupp.ext
  intro k
  simpa using ExpPoly.deriv_smul ν (-1) (P k)

theorem laplacian_neg (P : MildPoly) : laplacian (-P) = -laplacian P := by
  apply Finsupp.ext; intro k; simp

theorem deriv_duhamel (ν : ℚ) (P : MildPoly) :
    deriv ν (duhamel ν P) = P + ν • laplacian (duhamel ν P) := by
  apply Finsupp.ext
  intro k
  have h := ExpPoly.deriv_duhamel ν (heatRate k) (P k)
  have hr : (heatRate k : ℚ) = (lam k : ℚ) := by exact_mod_cast heatRate_cast k
  simp only [deriv_apply, duhamel_apply, Finsupp.add_apply,
    Finsupp.smul_apply, laplacian_apply, smul_smul]
  rw [hr] at h
  simpa only [sub_eq_add_neg, mul_neg, neg_smul] using eq_sub_of_add_eq h

theorem meanZero_heat {P : MildPoly} (hP : MeanZero P) : MeanZero (heat P) := by
  simp [MeanZero, show P 0 = 0 from hP]

theorem isEven_heat {P : MildPoly} (hP : IsEven P) : IsEven (heat P) := by
  intro k; simp [hP k]

theorem meanZero_duhamel (ν : ℚ) {P : MildPoly} (hP : MeanZero P) :
    MeanZero (duhamel ν P) := by simp [MeanZero, show P 0 = 0 from hP]

theorem isEven_duhamel (ν : ℚ) {P : MildPoly} (hP : IsEven P) :
    IsEven (duhamel ν P) := by intro k; simp [hP k]

/-- Every mode of `P` has size at most `K`. -/
def SizeLE (K : ℕ) (P : MildPoly) : Prop := ∀ k ∈ P.support, size k ≤ K

theorem SizeLE.mono {K K' : ℕ} (h : K ≤ K') {P : MildPoly} (hP : SizeLE K P) : SizeLE K' P :=
  fun k hk => (hP k hk).trans h

theorem sizeLE_zero (K : ℕ) : SizeLE K (0 : MildPoly) := fun k hk => by simp at hk

theorem sizeLE_add {K : ℕ} {P Q : MildPoly} (hP : SizeLE K P) (hQ : SizeLE K Q) :
    SizeLE K (P + Q) := fun k hk => by
  rcases Finset.mem_union.mp (Finsupp.support_add hk) with h | h
  · exact hP k h
  · exact hQ k h

theorem sizeLE_neg {K : ℕ} {P : MildPoly} (hP : SizeLE K P) : SizeLE K (-P) := fun k hk =>
  hP k (by simpa using hk)

theorem sizeLE_sub {K : ℕ} {P Q : MildPoly} (hP : SizeLE K P) (hQ : SizeLE K Q) :
    SizeLE K (P - Q) := by
  intro k hk
  rcases Finset.mem_union.mp (Finsupp.support_sub hk) with h | h
  · exact hP k h
  · exact hQ k h

theorem sizeLE_smul {K : ℕ} (c : ℚ) {P : MildPoly} (hP : SizeLE K P) : SizeLE K (c • P) :=
  fun k hk => hP k (Finsupp.support_smul hk)

theorem sizeLE_sum {ι : Type*} {K : ℕ} (s : Finset ι) {f : ι → MildPoly}
    (h : ∀ i ∈ s, SizeLE K (f i)) : SizeLE K (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sizeLE_zero K
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact sizeLE_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem sizeLE_transport {K K' : ℕ} {P Q : MildPoly} (hP : SizeLE K P) (hQ : SizeLE K' Q) :
    SizeLE (K + K') (transport P Q) := by
  intro k hk
  rw [Finsupp.mem_support_iff, transport_apply] at hk
  obtain ⟨p, hp, hp'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
  obtain ⟨q, hq, hq'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp'
  split_ifs at hq' with e
  · subst e
    exact (size_add_le p q).trans (add_le_add (hP p hp) (hQ q hq))
  · exact absurd rfl hq'

theorem sizeLE_heat {K : ℕ} {P : MildPoly} (hP : SizeLE K P) : SizeLE K (heat P) :=
  fun k hk => hP k (by
    rw [Finsupp.mem_support_iff] at hk ⊢
    exact fun hz => hk (by simp [hz]))

theorem sizeLE_duhamel (ν : ℚ) {K : ℕ} {P : MildPoly} (hP : SizeLE K P) :
    SizeLE K (duhamel ν P) := fun k hk => hP k (by
      rw [Finsupp.mem_support_iff] at hk ⊢
      exact fun hz => hk (by simp [hz]))

/-! ## The interaction-degree recursion -/

/-- The causal quadratic forcing, integrated in physical time. -/
noncomputable def rhs (ν : ℚ) (ω : Stream) : Stream := fun n =>
  -duhamel ν (∑ m ∈ Finset.range (n + 1), transport (ω m) (ω (n - m)))

theorem rhs_causal (ν : ℚ) : (shiftAxis MildPoly).IsCausal (rhs ν) := by
  intro k a b h n hn
  unfold rhs
  apply congrArg Neg.neg
  apply congrArg (duhamel ν)
  apply Finset.sum_congr rfl
  intro m hm
  rw [h m (by simp only [Finset.mem_range] at hm; omega), h (n - m) (by omega)]

/-- Wild's expansion as the unique causal solution from the heated initial slice. -/
noncomputable def wild (ν : ℚ) (boundary : Stream) : Stream :=
  (shiftAxis MildPoly).solution (rhs ν) (fun n => heat (boundary n))

@[simp] theorem wild_zero (ν : ℚ) (b : Stream) : wild ν b 0 = heat (b 0) :=
  (shiftAxis_agree_zero _ _).mp (Axis.solution_slice (rhs_causal ν))

/-- One more nonlinear interaction is a time-integrated transport convolution. -/
theorem wild_succ (ν : ℚ) (b : Stream) (n : ℕ) :
    wild ν b (n + 1) = -duhamel ν
      (∑ m ∈ Finset.range (n + 1), transport (wild ν b m) (wild ν b (n - m))) :=
  congrFun (Axis.solution_pde (rhs_causal ν)) n

/-- Existence in the reconstruction form used by the feedback circuit. -/
theorem wild_reconstructs (ν : ℚ) (b : Stream) :
    shiftFrom (rhs ν (wild ν b)) (fun n => heat (b n)) = wild ν b :=
  Axis.solution_reconstructs (boundary := fun n => heat (b n)) (rhs_causal ν)

/-- Uniqueness concerns interaction-degree streams, not arbitrary classical fields. -/
theorem wild_recursion_unique (ν : ℚ) (b a : Stream)
    (h0 : a 0 = heat (b 0))
    (hs : ∀ n, a (n + 1) = -duhamel ν
      (∑ m ∈ Finset.range (n + 1), transport (a m) (a (n - m)))) :
    a = wild ν b :=
  Axis.eq_solution (rhs_causal ν) a (funext hs) ((shiftAxis_agree_zero _ _).mpr h0)

/-- No positive interaction-degree boundary coefficient affects the solution. -/
theorem wild_congr_slice (ν : ℚ) (b b' : Stream) (h : b 0 = b' 0) :
    wild ν b = wild ν b' := by
  apply Axis.solution_congr_slice (rhs_causal ν)
  exact (shiftAxis_agree_zero _ _).mpr (congrArg heat h)

/-- The positive-degree terms satisfy the physical-time vorticity equation. -/
theorem deriv_wild_succ (ν : ℚ) (b : Stream) (n : ℕ) :
    deriv ν (wild ν b (n + 1)) = ν • laplacian (wild ν b (n + 1)) -
      ∑ m ∈ Finset.range (n + 1), transport (wild ν b m) (wild ν b (n - m)) := by
  rw [wild_succ, deriv_neg, deriv_duhamel, laplacian_neg]
  module

/-- Mean-zero starts remain mean zero in every interaction term. -/
theorem wild_meanZero (ν : ℚ) (b : Stream) (hb : MeanZero (b 0)) (n : ℕ) :
    MeanZero (wild ν b n) := by
  cases n with
  | zero => simpa using meanZero_heat hb
  | succ n =>
      rw [wild_succ]
      have h := meanZero_duhamel ν (meanZero_sum (Finset.range (n + 1))
        (fun m _ => meanZero_transport (wild ν b m) (wild ν b (n - m))))
      change -(duhamel ν _ 0) = 0
      rw [show duhamel ν _ 0 = 0 from h, neg_zero]

/-- Even starts remain even, representing real cosine fields. -/
theorem wild_isEven (ν : ℚ) (b : Stream) (hb : IsEven (b 0)) (n : ℕ) :
    IsEven (wild ν b n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simpa using isEven_heat hb
      | succ n =>
          rw [wild_succ]
          have h := isEven_duhamel ν (isEven_sum (Finset.range (n + 1)) (fun m hm =>
            isEven_transport (ih m (Finset.mem_range.mp hm)) (ih (n - m) (by omega))))
          intro k
          simp only [Finsupp.neg_apply, h k]

/-- Interaction degree n has no modes larger than (n+1) times the initial size. -/
theorem wild_sizeLE (ν : ℚ) (b : Stream) (K : ℕ) (hb : SizeLE K (b 0)) (n : ℕ) :
    SizeLE ((n + 1) * K) (wild ν b n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero => simpa using sizeLE_heat hb
      | succ n =>
          rw [wild_succ]
          apply sizeLE_neg
          apply sizeLE_duhamel
          apply sizeLE_sum
          intro m hm
          have hm' := Finset.mem_range.mp hm
          have h := sizeLE_transport (ih m hm') (ih (n - m) (by omega))
          have he : (m + 1) * K + (n - m + 1) * K = (n + 1 + 1) * K := by
            rw [← add_mul]
            congr 1
            omega
          simpa only [he] using h

#print axioms wild_recursion_unique
#print axioms deriv_wild_succ
#print axioms wild_meanZero
#print axioms wild_isEven
#print axioms wild_sizeLE

end Gimle.Asgard.Streams.Mild
