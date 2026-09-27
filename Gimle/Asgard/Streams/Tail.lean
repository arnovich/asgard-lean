import Gimle.Asgard.Streams.Realization
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Certified analytic truncation of streams

A formal stream is only a coefficient family; its type says nothing about
convergence. This module turns an explicit, *proved* coefficient majorant into
analytic convergence and a uniform rectangular truncation error.

Supplied data (all exact rationals):

* a `Majorant`: `M ≥ 0` and radii `R_i > 0`;
* a `Box`: radii `r_i ≥ 0`, the domain `|x_i| ≤ r_i`, strictly inside the
  majorant: `r_i < R_i` (boundary radii are rejected);
* a proof `Majorizes basis a m` that **every** decoded OGF coefficient obeys
  `|a_α| ≤ M · ∏ᵢ R_i^(−α_i)`.

`TailCertificate basis a` bundles exactly these. From it:

* `TailCertificate.hasSum`: at every point of the box the series
  `Σ_α a_α x^α` of decoded coefficients converges absolutely, to `analyticField`;
* `TailCertificate.truncationBound`: uniformly on the box,
  `|analyticField − windowField| ≤ tailBound`, where `windowField` is the finite
  sum over the rectangle `α_i < N_i` and, with `q_i = r_i / R_i`,
  `tailBound = M · (Σᵢ q_i^N_i) · ∏ᵢ (1 − q_i)⁻¹`.

The error metric is the absolute difference of the evaluated real scalar field,
uniform over the closed box. It is neither a coefficientwise error nor a
statistical confidence. Several output ports combine in the sup norm
(`truncationBound_ports`). The window field is the real field of a polynomial
realizing the truncated stream (`truncate_realizes`, `field_windowPoly`).

Coefficients are always decoded, so the whole construction depends on the OGF
series only: `analyticField_encode`, `majorizes_encode`. -/
namespace Gimle.Asgard.Streams

/-! ## Absolutely summable products over multi-indices -/

private theorem hasSum_pi_prod_aux (d : Nat) : ∀ (f : Fin d → ℕ → ℝ) (s : Fin d → ℝ),
    (∀ i, Summable fun k => ‖f i k‖) → (∀ i, HasSum (f i) (s i)) →
    HasSum (fun k : Fin d → ℕ => ∏ i, f i (k i)) (∏ i, s i) ∧
      Summable fun k : Fin d → ℕ => ‖∏ i, f i (k i)‖ := by
  induction d with
  | zero =>
      intro f s _ _
      simp only [Finset.univ_eq_empty, Finset.prod_empty, norm_one]
      have h : HasSum (fun _ : Fin 0 → ℕ => (1 : ℝ)) 1 :=
        hasSum_single (f := fun _ : Fin 0 → ℕ => (1 : ℝ)) Fin.elim0
          (fun b ne => (ne (Subsingleton.elim _ _)).elim)
      exact ⟨h, h.summable⟩
  | succ d ih =>
      intro f s norms sums
      obtain ⟨hs, hn⟩ := ih (fun i => f i.succ) (fun i => s i.succ)
        (fun i => norms i.succ) (fun i => sums i.succ)
      let e : ℕ × (Fin d → ℕ) ≃ (Fin (d + 1) → ℕ) := Fin.consEquiv (fun _ => ℕ)
      have comp : ∀ p : ℕ × (Fin d → ℕ),
          (∏ i, f i (e p i)) = f 0 p.1 * ∏ i : Fin d, f i.succ (p.2 i) := by
        intro p
        rw [Fin.prod_univ_succ]
        rfl
      have prod := (sums 0).mul hs (summable_mul_of_summable_norm (R := ℝ) (f := f 0)
        (g := fun k : Fin d → ℕ => ∏ i : Fin d, f i.succ (k i)) (norms 0) hn)
      have prodn : Summable fun p : ℕ × (Fin d → ℕ) =>
          ‖f 0 p.1‖ * ‖∏ i : Fin d, f i.succ (p.2 i)‖ :=
        summable_mul_of_summable_norm (f := fun k => ‖f 0 k‖)
          (g := fun k : Fin d → ℕ => ‖∏ i : Fin d, f i.succ (k i)‖)
          (by simpa using norms 0) (by simpa using hn)
      refine ⟨?_, ?_⟩
      · rw [Fin.prod_univ_succ, ← e.hasSum_iff]
        exact prod.congr_fun fun p => comp p
      · rw [← e.summable_iff]
        refine prodn.congr fun p => ?_
        simp only [Function.comp_apply, comp p, norm_mul]

/-- A finite product of absolutely summable one-axis families is summable over
multi-indices, to the product of the sums. -/
theorem hasSum_index_prod {d : Nat} (f : Fin d → ℕ → ℝ) (s : Fin d → ℝ)
    (norms : ∀ i, Summable fun k => ‖f i k‖) (sums : ∀ i, HasSum (f i) (s i)) :
    HasSum (fun α : Index d => ∏ i, f i (α i)) (∏ i, s i) := by
  rw [← (Finsupp.equivFunOnFinite (α := Fin d) (M := ℕ)).symm.hasSum_iff]
  exact (hasSum_pi_prod_aux d f s norms sums).1


private theorem hasSum_geometric_index {d : Nat} (q : Fin d → ℝ) (h0 : ∀ i, 0 ≤ q i)
    (h1 : ∀ i, q i < 1) :
    HasSum (fun α : Index d => ∏ i, q i ^ α i) (∏ i, (1 - q i)⁻¹) :=
  hasSum_index_prod _ _
    (fun i => by
      simpa [norm_pow, Real.norm_of_nonneg (h0 i)] using summable_geometric_of_lt_one (h0 i) (h1 i))
    (fun i => hasSum_geometric_of_lt_one (h0 i) (h1 i))

/-- The geometric tail `Σ_{k ≥ N} q^k = q^N / (1 − q)` on one axis. -/
private theorem hasSum_geometric_tail {q : ℝ} (h0 : 0 ≤ q) (h1 : q < 1) (N : ℕ) :
    HasSum (fun k : ℕ => if N ≤ k then q ^ k else 0) (q ^ N * (1 - q)⁻¹) := by
  rw [← hasSum_nat_add_iff' N]
  have zero : ∑ i ∈ Finset.range N, (if N ≤ i then q ^ i else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => if_neg (by simpa using hi)
  rw [zero, sub_zero]
  refine ((hasSum_geometric_of_lt_one h0 h1).mul_left (q ^ N)).congr_fun fun k => ?_
  simp [pow_add, mul_comm]

/-! ## Contract data -/

/-- A supplied coefficient majorant: exact `M ≥ 0` and radii `R_i > 0`. The
inequality it asserts is the separate premise `Majorizes`. -/
structure Majorant (d : Nat) where
  /-- `M` -/
  bound : ℚ
  /-- `R_i`, one per ordered axis -/
  radius : Fin d → ℚ
  bound_nonneg : 0 ≤ bound
  radius_pos : ∀ i, 0 < radius i

/-- A closed box `|x_i| ≤ r_i` with exact radii `r_i ≥ 0` (zero allowed). -/
structure Box (d : Nat) where
  /-- `r_i`, one per ordered axis -/
  radius : Fin d → ℚ
  radius_nonneg : ∀ i, 0 ≤ radius i

/-- The real point `x` lies in the closed box. -/
def Box.Mem {d : Nat} (b : Box d) (x : Fin d → ℝ) : Prop :=
  ∀ i, |x i| ≤ b.radius i

/-- The majorant premise, over **every** multi-index of the whole stream:
`|a_α| ≤ M · ∏ᵢ R_i^(−α_i)` for the decoded (OGF) coefficients `a_α`. -/
def Majorizes {d : Nat} (basis : Basis) (a : Stream d) (m : Majorant d) : Prop :=
  ∀ α : Index d, |decode basis a α| ≤ m.bound * ∏ i, (m.radius i ^ α i)⁻¹

/-- `q_i = r_i / R_i`. -/
def ratio {d : Nat} (m : Majorant d) (b : Box d) (i : Fin d) : ℚ :=
  b.radius i / m.radius i

/-- The conservative rational error `M · (Σᵢ q_i^N_i) · ∏ᵢ (1 − q_i)⁻¹`: a union
bound over the axes along which an omitted index leaves the window. -/
def tailBound {d : Nat} (m : Majorant d) (b : Box d) (N : Fin d → ℕ) : ℚ :=
  m.bound * (∑ i, ratio m b i ^ N i) * ∏ i, (1 - ratio m b i)⁻¹

/-! ## The analytic field and its rectangular window -/

/-- The term `a_α · x^α` of the decoded series at the real point `x`. -/
noncomputable def seriesTerm {d : Nat} (basis : Basis) (a : Stream d) (x : Fin d → ℝ)
    (α : Index d) : ℝ :=
  (decode basis a α : ℝ) * ∏ i, x i ^ α i

/-- The analytic field `Σ_α a_α x^α`. It is an unconditional `tsum`, so it is
meaningful only where summability is proved: no convergence follows from the
stream alone (`TailCertificate.hasSum` supplies it). -/
noncomputable def analyticField {d : Nat} (basis : Basis) (a : Stream d) (x : Fin d → ℝ) : ℝ :=
  ∑' α, seriesTerm basis a x α

/-- The rectangular window `α_i < N_i` of multi-indices (empty if some `N_i = 0`). -/
noncomputable def window {d : Nat} (N : Fin d → ℕ) : Finset (Index d) :=
  (Fintype.piFinset fun i => Finset.range (N i)).map
    (Finsupp.equivFunOnFinite (α := Fin d) (M := ℕ)).symm.toEmbedding

theorem mem_window {d : Nat} (N : Fin d → ℕ) (α : Index d) :
    α ∈ window N ↔ ∀ i, α i < N i := by
  simp only [window, Finset.mem_map_equiv, Equiv.symm_symm, Fintype.mem_piFinset,
    Finset.mem_range, Finsupp.equivFunOnFinite_apply]

/-- The finite sum of the decoded series over the window. -/
noncomputable def windowField {d : Nat} (basis : Basis) (N : Fin d → ℕ) (a : Stream d)
    (x : Fin d → ℝ) : ℝ :=
  ∑ α ∈ window N, seriesTerm basis a x α

/-! ## Majorant ⇒ absolute convergence -/

section Bound

variable {d : Nat} {basis : Basis} {a : Stream d} {m : Majorant d} {b : Box d}

private theorem ratio_nonneg (i : Fin d) : (0 : ℝ) ≤ (ratio m b i : ℝ) := by
  exact_mod_cast div_nonneg (b.radius_nonneg i) (m.radius_pos i).le

private theorem ratio_lt_one (inside : ∀ i, b.radius i < m.radius i) (i : Fin d) :
    (ratio m b i : ℝ) < 1 := by
  exact_mod_cast (div_lt_one (m.radius_pos i)).mpr (inside i)

/-- Each term is dominated by the geometric family `M · ∏ q_i^α_i`. -/
theorem norm_seriesTerm_le (majorizes : Majorizes basis a m) {x : Fin d → ℝ} (hx : b.Mem x)
    (α : Index d) :
    ‖seriesTerm basis a x α‖ ≤ (m.bound : ℝ) * ∏ i, (ratio m b i : ℝ) ^ α i := by
  have coeff : |(decode basis a α : ℝ)| ≤ (m.bound : ℝ) * (∏ i, ((m.radius i : ℝ) ^ α i)⁻¹) := by
    have h : ((|decode basis a α| : ℚ) : ℝ) ≤
        ((m.bound * (∏ i, (m.radius i ^ α i)⁻¹) : ℚ) : ℝ) := by
      exact_mod_cast majorizes α
    push_cast at h
    exact h
  have mono : ∏ i, |x i| ^ α i ≤ ∏ i, (b.radius i : ℝ) ^ α i :=
    Finset.prod_le_prod (fun i _ => by positivity)
      (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hx i) _)
  have rhs : (m.bound : ℝ) * (∏ i, ((m.radius i : ℝ) ^ α i)⁻¹) * ∏ i, (b.radius i : ℝ) ^ α i =
      (m.bound : ℝ) * ∏ i, (ratio m b i : ℝ) ^ α i := by
    rw [mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [ratio, Rat.cast_div, div_pow]
    ring
  rw [Real.norm_eq_abs, seriesTerm, abs_mul, Finset.abs_prod]
  simp only [abs_pow]
  rw [← rhs]
  have hb : (0 : ℝ) ≤ m.bound := by exact_mod_cast m.bound_nonneg
  refine mul_le_mul coeff mono (Finset.prod_nonneg fun i _ => by positivity) ?_
  refine mul_nonneg hb (Finset.prod_nonneg fun i _ => inv_nonneg.mpr (pow_nonneg ?_ _))
  exact_mod_cast (m.radius_pos i).le

/-- Absolute convergence at every point of the box. -/
theorem summable_norm_seriesTerm (majorizes : Majorizes basis a m)
    (inside : ∀ i, b.radius i < m.radius i) {x : Fin d → ℝ} (hx : b.Mem x) :
    Summable fun α => ‖seriesTerm basis a x α‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_seriesTerm_le majorizes hx)
    ((hasSum_geometric_index _ (fun i => ratio_nonneg (m := m) (b := b) i)
      (ratio_lt_one inside)).summable.mul_left _)

/-- The series of decoded coefficients sums to `analyticField` on the box. -/
theorem hasSum_analyticField (majorizes : Majorizes basis a m)
    (inside : ∀ i, b.radius i < m.radius i) {x : Fin d → ℝ} (hx : b.Mem x) :
    HasSum (seriesTerm basis a x) (analyticField basis a x) :=
  (summable_norm_seriesTerm majorizes inside hx).of_norm.hasSum

/-- One-axis dominating factor for the part of the tail leaving the window along `i`. -/
private noncomputable def tailFactor (m : Majorant d) (b : Box d) (N : Fin d → ℕ) (i j : Fin d)
    (k : ℕ) : ℝ :=
  if j = i then (if N j ≤ k then (ratio m b j : ℝ) ^ k else 0) else (ratio m b j : ℝ) ^ k

private theorem tailFactor_nonneg (N : Fin d → ℕ) (i j : Fin d) (k : ℕ) :
    0 ≤ tailFactor m b N i j k := by
  unfold tailFactor
  have := ratio_nonneg (m := m) (b := b) j
  split_ifs <;> positivity

private theorem hasSum_tailFactor (inside : ∀ i, b.radius i < m.radius i) (N : Fin d → ℕ)
    (i : Fin d) :
    HasSum (fun α : Index d => ∏ j, tailFactor m b N i j (α j))
      ((ratio m b i : ℝ) ^ N i * ∏ j, (1 - (ratio m b j : ℝ))⁻¹) := by
  have sums : ∀ j, HasSum (tailFactor m b N i j)
      (if j = i then (ratio m b j : ℝ) ^ N j * (1 - (ratio m b j : ℝ))⁻¹
        else (1 - (ratio m b j : ℝ))⁻¹) := by
    intro j
    unfold tailFactor
    split_ifs
    · exact hasSum_geometric_tail (ratio_nonneg j) (ratio_lt_one inside j) (N j)
    · exact hasSum_geometric_of_lt_one (ratio_nonneg j) (ratio_lt_one inside j)
  have h := hasSum_index_prod _ _ (fun j => by
      simpa [Real.norm_of_nonneg (tailFactor_nonneg N i j _)] using (sums j).summable) sums
  convert h using 1
  have split : (∏ j, if j = i then (ratio m b j : ℝ) ^ N j * (1 - (ratio m b j : ℝ))⁻¹
      else (1 - (ratio m b j : ℝ))⁻¹) =
      (∏ j, if j = i then (ratio m b j : ℝ) ^ N j else 1) * ∏ j, (1 - (ratio m b j : ℝ))⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by split_ifs <;> simp
  rw [split, Finset.prod_ite_eq']
  simp

/-- **Uniform rectangular truncation bound.** On the box, the analytic field and
its window sum differ by at most `tailBound`. -/
theorem abs_analyticField_sub_windowField_le (majorizes : Majorizes basis a m)
    (inside : ∀ i, b.radius i < m.radius i) (N : Fin d → ℕ) {x : Fin d → ℝ} (hx : b.Mem x) :
    |analyticField basis a x - windowField basis N a x| ≤ tailBound m b N := by
  classical
  have hF := hasSum_analyticField majorizes inside hx
  have hW : HasSum (fun α => if α ∈ window N then seriesTerm basis a x α else 0)
      (windowField basis N a x) := by
    have h : HasSum (fun α => if α ∈ window N then seriesTerm basis a x α else 0)
        (∑ α ∈ window N, if α ∈ window N then seriesTerm basis a x α else 0) :=
      hasSum_sum_of_ne_finset_zero fun α hα => if_neg hα
    rw [Finset.sum_congr rfl fun α hα => if_pos hα] at h
    exact h
  have hT : HasSum (fun α => if α ∈ window N then 0 else seriesTerm basis a x α)
      (analyticField basis a x - windowField basis N a x) :=
    (hF.sub hW).congr_fun fun α => by split_ifs <;> simp
  let D : Index d → ℝ := fun α =>
    (m.bound : ℝ) * ∑ i, ∏ j, tailFactor m b N i j (α j)
  have hD : HasSum D (tailBound m b N : ℝ) := by
    have h := (hasSum_sum (s := Finset.univ) fun i _ => hasSum_tailFactor inside N i).mul_left
      (m.bound : ℝ)
    have e : (tailBound m b N : ℝ) = (m.bound : ℝ) *
        ∑ i, (ratio m b i : ℝ) ^ N i * ∏ j, (1 - (ratio m b j : ℝ))⁻¹ := by
      simp only [tailBound]
      push_cast
      rw [mul_assoc, Finset.sum_mul]
    rw [e]
    exact h
  have hb : (0 : ℝ) ≤ m.bound := by exact_mod_cast m.bound_nonneg
  have dominated : ∀ α, |if α ∈ window N then 0 else seriesTerm basis a x α| ≤ D α := by
    intro α
    have D_nonneg : 0 ≤ D α := mul_nonneg hb (Finset.sum_nonneg fun i _ =>
      Finset.prod_nonneg fun j _ => tailFactor_nonneg N i j _)
    split_ifs with hα
    · simpa using D_nonneg
    · rw [mem_window] at hα
      push Not at hα
      obtain ⟨i, hi⟩ := hα
      have exact : ∏ j, (ratio m b j : ℝ) ^ α j = ∏ j, tailFactor m b N i j (α j) := by
        refine Finset.prod_congr rfl fun j _ => ?_
        unfold tailFactor
        split_ifs with h1 h2
        · rfl
        · exact absurd (h1 ▸ hi) h2
        · rfl
      calc |seriesTerm basis a x α| = ‖seriesTerm basis a x α‖ := (Real.norm_eq_abs _).symm
        _ ≤ (m.bound : ℝ) * ∏ j, (ratio m b j : ℝ) ^ α j := norm_seriesTerm_le majorizes hx α
        _ ≤ D α := by
          rw [exact]
          refine mul_le_mul_of_nonneg_left ?_ hb
          exact Finset.single_le_sum (f := fun i => ∏ j, tailFactor m b N i j (α j))
            (fun i _ => Finset.prod_nonneg fun j _ => tailFactor_nonneg N i j _)
            (Finset.mem_univ i)
  refine abs_le.mpr ⟨?_, ?_⟩
  · exact hasSum_le (fun α => neg_le_of_abs_le (dominated α)) hD.neg hT
  · exact hasSum_le (fun α => le_of_abs_le (dominated α)) hT hD

end Bound

/-! ## The certificate and its conclusion -/

/-- Everything the truncation theorem needs, and nothing inferred: the exact
majorant, the box strictly inside it, and the proof that **every** decoded
coefficient of `a` obeys it. Without `majorizes` there is no certificate. -/
structure TailCertificate {d : Nat} (basis : Basis) (a : Stream d) where
  majorant : Majorant d
  box : Box d
  /-- `r_i < R_i`: boundary radii are rejected. -/
  inside : ∀ i, box.radius i < majorant.radius i
  majorizes : Majorizes basis a majorant

/-- The certified conclusion, naming the original stream `a`, its basis, the
ordered axes `Fin d`, the domain (closed box `b`), the window `N` and the error
`ε`: uniformly on `b`, the absolute error of the evaluated scalar field is at
most `ε`. -/
def TruncationBound {d : Nat} (basis : Basis) (a : Stream d) (b : Box d) (N : Fin d → ℕ)
    (ε : ℚ) : Prop :=
  ∀ x, b.Mem x → |analyticField basis a x - windowField basis N a x| ≤ ε

namespace TailCertificate

variable {d : Nat} {basis : Basis} {a : Stream d}

/-- The certified error at window `N`: `tailBound` of the certificate's own
majorant and box. -/
def error (c : TailCertificate basis a) (N : Fin d → ℕ) : ℚ :=
  tailBound c.majorant c.box N

/-- Absolute convergence on the certificate's box. -/
theorem summable_norm (c : TailCertificate basis a) {x : Fin d → ℝ} (hx : c.box.Mem x) :
    Summable fun α => ‖seriesTerm basis a x α‖ :=
  summable_norm_seriesTerm c.majorizes c.inside hx

/-- Convergence to the analytic field on the certificate's box. -/
theorem hasSum (c : TailCertificate basis a) {x : Fin d → ℝ} (hx : c.box.Mem x) :
    HasSum (seriesTerm basis a x) (analyticField basis a x) :=
  hasSum_analyticField c.majorizes c.inside hx

/-- **Main theorem.** A certificate for `a` bounds the rectangular truncation
at every window, uniformly on its box, by its `tailBound`. -/
theorem truncationBound (c : TailCertificate basis a) (N : Fin d → ℕ) :
    TruncationBound basis a c.box N (c.error N) :=
  fun _ hx => abs_analyticField_sub_windowField_le c.majorizes c.inside N hx

end TailCertificate

/-- Transport through the bound: a lower bound `L` of the window field gives the
lower bound `L − ε` of the analytic field, and symmetrically. -/
theorem TruncationBound.lower {d : Nat} {basis : Basis} {a : Stream d} {b : Box d}
    {N : Fin d → ℕ} {ε : ℚ} (h : TruncationBound basis a b N ε) {x : Fin d → ℝ} (hx : b.Mem x)
    {L : ℝ} (hL : L ≤ windowField basis N a x) : L - ε ≤ analyticField basis a x := by
  have := abs_le.mp (h x hx)
  linarith [this.1]

theorem TruncationBound.upper {d : Nat} {basis : Basis} {a : Stream d} {b : Box d}
    {N : Fin d → ℕ} {ε : ℚ} (h : TruncationBound basis a b N ε) {x : Fin d → ℝ} (hx : b.Mem x)
    {U : ℝ} (hU : windowField basis N a x ≤ U) : analyticField basis a x ≤ U + ε := by
  have := abs_le.mp (h x hx)
  linarith [this.2]

/-- A larger error still bounds. -/
theorem TruncationBound.mono {d : Nat} {basis : Basis} {a : Stream d} {b : Box d}
    {N : Fin d → ℕ} {ε ε' : ℚ} (h : TruncationBound basis a b N ε) (le : ε ≤ ε') :
    TruncationBound basis a b N ε' :=
  fun x hx => (h x hx).trans (by exact_mod_cast le)

/-- **Several output ports.** Per-port bounds `ε_j` on a shared box combine in the
sup norm of `ℝⁿ` (mathlib's norm on `Fin n → ℝ`): the vector error is at most any
common `B ≥ ε_j`. Other norms need their own combination (e.g. `Σ ε_j` for ℓ¹). -/
theorem truncationBound_ports {d n : Nat} {basis : Basis} {a : StreamPoint d n} {b : Box d}
    {N : Fin d → ℕ} {ε : Fin n → ℚ} (h : ∀ j, TruncationBound basis (a j) b N (ε j))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ j, (ε j : ℝ) ≤ B) {x : Fin d → ℝ} (hx : b.Mem x) :
    ‖fun j => analyticField basis (a j) x - windowField basis N (a j) x‖ ≤ B := by
  refine (pi_norm_le_iff_of_nonneg hB0).mpr fun j => ?_
  rw [Real.norm_eq_abs]
  exact (h j x hx).trans (hB j)

/-! ## Representation invariance -/

section Invariance

variable {d : Nat}

/-- Everything reads decoded coefficients: equal decoded streams have equal terms. -/
theorem seriesTerm_eq_of_decode {basis basis' : Basis} {a a' : Stream d}
    (h : decode basis a = decode basis' a') : seriesTerm basis a = seriesTerm basis' a' := by
  funext x α
  simp only [seriesTerm, h]

theorem analyticField_eq_of_decode {basis basis' : Basis} {a a' : Stream d}
    (h : decode basis a = decode basis' a') : analyticField basis a = analyticField basis' a' := by
  funext x
  simp only [analyticField, seriesTerm_eq_of_decode h]

theorem windowField_eq_of_decode {basis basis' : Basis} {a a' : Stream d}
    (h : decode basis a = decode basis' a') (N : Fin d → ℕ) :
    windowField basis N a = windowField basis' N a' := by
  funext x
  simp only [windowField, seriesTerm_eq_of_decode h]

theorem majorizes_iff_of_decode {basis basis' : Basis} {a a' : Stream d}
    (h : decode basis a = decode basis' a') (m : Majorant d) :
    Majorizes basis a m ↔ Majorizes basis' a' m := by
  simp only [Majorizes, h]

theorem truncationBound_iff_of_decode {basis basis' : Basis} {a a' : Stream d}
    (h : decode basis a = decode basis' a') (b : Box d) (N : Fin d → ℕ) (ε : ℚ) :
    TruncationBound basis a b N ε ↔ TruncationBound basis' a' b N ε := by
  simp only [TruncationBound, analyticField_eq_of_decode h, windowField_eq_of_decode h]

/-- The same series stored in either basis (`encode basis c` has OGF series `c`)
has the same analytic field, window field and majorant premise. -/
theorem analyticField_encode (basis : Basis) (c : Stream d) :
    analyticField basis (encode basis c) = analyticField .ogf c :=
  analyticField_eq_of_decode (by rw [decode_encode]; rfl)

theorem windowField_encode (basis : Basis) (N : Fin d → ℕ) (c : Stream d) :
    windowField basis N (encode basis c) = windowField .ogf N c :=
  windowField_eq_of_decode (by rw [decode_encode]; rfl) N

theorem majorizes_encode (basis : Basis) (c : Stream d) (m : Majorant d) :
    Majorizes basis (encode basis c) m ↔ Majorizes .ogf c m :=
  majorizes_iff_of_decode (by rw [decode_encode]; rfl) m

/-- A certificate moves between representations of the same decoded series,
with the same majorant, box and hence the same error. -/
def TailCertificate.transport {basis basis' : Basis} {a a' : Stream d}
    (h : decode basis a = decode basis' a') (c : TailCertificate basis a) :
    TailCertificate basis' a' :=
  { c with majorizes := (majorizes_iff_of_decode h c.majorant).mp c.majorizes }

@[simp] theorem TailCertificate.transport_error {basis basis' : Basis} {a a' : Stream d}
    (h : decode basis a = decode basis' a') (c : TailCertificate basis a) (N : Fin d → ℕ) :
    (c.transport h).error N = c.error N := rfl

end Invariance

/-! ## Degenerate radii and axes -/

/-- At the origin the analytic field is the constant coefficient, with no
majorant needed: every other term vanishes. -/
theorem analyticField_zero {d : Nat} (basis : Basis) (a : Stream d) :
    analyticField basis a 0 = decode basis a 0 := by
  rw [analyticField, tsum_eq_single 0]
  · simp [seriesTerm]
  · intro α hα
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra h
      push Not at h
      exact hα (Finsupp.ext h)
    simp only [seriesTerm, Pi.zero_apply]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (zero_pow hi), mul_zero]

/-- A zero-radius box contains only the origin. -/
theorem Box.mem_of_radius_zero {d : Nat} {b : Box d} (h : ∀ i, b.radius i = 0)
    {x : Fin d → ℝ} (hx : b.Mem x) : x = 0 := by
  funext i
  have := hx i
  rw [h i, Rat.cast_zero] at this
  exact abs_nonpos_iff.mp this

/-- A zero-radius box and a positive window give zero error. -/
theorem tailBound_radius_zero {d : Nat} (m : Majorant d) (b : Box d)
    (h : ∀ i, b.radius i = 0) (N : Fin d → ℕ) (pos : ∀ i, 0 < N i) : tailBound m b N = 0 := by
  have : ∀ i, ratio m b i ^ N i = 0 := fun i => by
    rw [ratio, h i, zero_div, zero_pow (pos i).ne']
  simp [tailBound, this]

/-- With no axes the tail is empty: the error is zero. -/
@[simp] theorem tailBound_axes_zero (m : Majorant 0) (b : Box 0) (N : Fin 0 → ℕ) :
    tailBound m b N = 0 := by
  simp [tailBound]

/-- With no axes the window holds the single index, the constant. -/
theorem window_axes_zero (N : Fin 0 → ℕ) : window N = {0} := by
  ext α
  simp only [mem_window, IsEmpty.forall_iff, true_iff, Finset.mem_singleton]
  exact Subsingleton.elim _ _

/-! ## The window as a polynomial stream -/

theorem decode_truncate {d : Nat} (basis : Basis) (N : Fin d → ℕ) (a : Stream d) :
    decode basis (truncate N a) = truncate N (decode basis a) := by
  cases basis with
  | ogf => rfl
  | egf =>
      funext α
      change (truncate N a α) / factorial α = truncate N (fun n => a n / factorial n) α
      simp only [truncate]
      split_ifs <;> simp

/-- The window polynomial: decoded coefficients inside the window, zero outside. -/
noncomputable def windowPoly {d : Nat} (basis : Basis) (N : Fin d → ℕ) (a : Stream d) : Poly d :=
  polyOfCoeffs (window N) (decode basis (truncate N a))

theorem coeff_windowPoly {d : Nat} (basis : Basis) (N : Fin d → ℕ) (a : Stream d) (α : Index d) :
    MvPolynomial.coeff α (windowPoly basis N a) = decode basis (truncate N a) α := by
  refine coeff_polyOfCoeffs _ _ (fun n hn => ?_) α
  rw [mem_window]
  by_contra out
  apply hn
  rw [decode_truncate]
  simp only [truncate]
  exact if_neg out

/-- The truncated stream is polynomially realized, in its own basis. -/
theorem truncate_realizes {d : Nat} (basis : Basis) (N : Fin d → ℕ) (a : Stream d) :
    Realizes basis (truncate N a) (windowPoly basis N a) := by
  unfold Realizes ofPoly
  have : ((windowPoly basis N a : Poly d) : MvPowerSeries (Fin d) ℚ) =
      decode basis (truncate N a) := by
    ext α
    rw [MvPolynomial.coeff_coe, coeff_windowPoly]
    rfl
  rw [this, encode_decode]

/-- The window field is the real field of that polynomial. -/
theorem field_windowPoly {d : Nat} (basis : Basis) (N : Fin d → ℕ) (a : Stream d)
    (x : Fin d → ℝ) : field (windowPoly basis N a) x = windowField basis N a x := by
  simp only [field, windowPoly, polyOfCoeffs, map_sum, MvPolynomial.aeval_monomial, windowField,
    seriesTerm]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), decode_truncate]
  simp only [truncate, if_pos ((mem_window N α).mp hα)]
  rfl

/-- The window field is also the analytic field of the truncated stream: a
finite sum, with no majorant needed. -/
theorem analyticField_truncate {d : Nat} (basis : Basis) (N : Fin d → ℕ) (a : Stream d)
    (x : Fin d → ℝ) : analyticField basis (truncate N a) x = windowField basis N a x := by
  rw [analyticField, tsum_eq_sum (s := window N)]
  · refine Finset.sum_congr rfl fun α hα => ?_
    simp only [seriesTerm, decode_truncate, truncate, if_pos ((mem_window N α).mp hα)]
  · intro α hα
    rw [mem_window] at hα
    simp only [seriesTerm, decode_truncate, truncate, if_neg hα, Rat.cast_zero, zero_mul]

/-! ## Finite prefixes certify nothing -/

private theorem encode_apply_congr {d : Nat} (basis : Basis) {f g : Stream d} {α : Index d}
    (h : f α = g α) : encode basis f α = encode basis g α := by
  cases basis with
  | ogf => exact h
  | egf => change factorial α * f α = factorial α * g α; rw [h]

/-- **No finite set of coefficients certifies a majorant.** With at least one
axis, for any finite set `S` of observed indices and any majorant, some stream
agrees with `a` on all of `S` yet violates the majorant: an unobserved
coefficient can be arbitrarily large. -/
theorem prefix_cannot_certify {d : Nat} (basis : Basis) (a : Stream (d + 1))
    (S : Finset (Index (d + 1))) (m : Majorant (d + 1)) :
    ∃ a' : Stream (d + 1), (∀ α ∈ S, a' α = a α) ∧ ¬ Majorizes basis a' m := by
  classical
  let β : Index (d + 1) := Finsupp.single 0 (S.sup (fun α => α 0) + 1)
  have fresh : β ∉ S := by
    intro mem
    have := Finset.le_sup (f := fun α : Index (d + 1) => α 0) mem
    simp only [β, Finsupp.single_eq_same] at this
    omega
  let v : ℚ := m.bound * (∏ i, (m.radius i ^ β i)⁻¹) + 1
  refine ⟨encode basis (Function.update (decode basis a) β v), fun α hα => ?_, fun maj => ?_⟩
  · have ne : α ≠ β := fun h => fresh (h ▸ hα)
    rw [encode_apply_congr basis (g := decode basis a) (Function.update_of_ne ne _ _),
      encode_decode]
  · have h := maj β
    rw [decode_encode, Function.update_self] at h
    have nonneg : 0 ≤ m.bound * ∏ i, (m.radius i ^ β i)⁻¹ :=
      mul_nonneg m.bound_nonneg (Finset.prod_nonneg fun i _ =>
        inv_nonneg.mpr (pow_nonneg (m.radius_pos i).le _))
    rw [abs_of_pos (by positivity)] at h
    linarith

end Gimle.Asgard.Streams
