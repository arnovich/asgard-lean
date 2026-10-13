import Gimle.Asgard.Streams.TrigNorm
import Gimle.Asgard.Streams.Vorticity

/-! # Computing the vorticity stream's coefficients

`TrigPoly` is a `Finsupp`, which the kernel cannot evaluate. A `Table` is a
list of `(mode, coefficient)` pairs standing for the sum of the singles it
lists, with duplicates allowed and `normalize` merging them; on tables the
Laplacian, scalar multiples and the transport compute, and `toTrig` carries
each operation to the trigonometric polynomial it stands for (namespace
`Torus.Table`). `Table.absSum`, the sum of the absolute entries, bounds the ℓ¹
norm of the polynomial (`l1_le_absSum`, an inequality: duplicates may
overcount), and `sizeLE_toTrig` bounds its modes. The Picard iteration of
`NS.stream` in the OGF reading is then mirrored on finite sequences of tables
(`NS.picard`), each right-hand side normalised so that the tables stay small
and `absSum` of a Picard table is the ℓ¹ norm itself, and `NS.stream_coeff` says that the exact
coefficient of the stream at `t`-degree `n` and mode `k` is the rational the
kernel reads off the table, so a claimed value is checked by `decide +kernel`
and a wrong one is refuted the same way. Nothing is trusted from outside: the
table is computed inside the proof. -/
namespace Gimle.Asgard.Streams.Torus

/-- A finite sum of single modes, as a list of `(mode, coefficient)` pairs. -/
abbrev Table := List (Wave × ℚ)

namespace Table

/-- The trigonometric polynomial a table stands for. -/
noncomputable def toTrig (l : Table) : TrigPoly := (l.map fun e => Finsupp.single e.1 e.2).sum

/-- The coefficient at `k`: the sum of the entries listed at `k`. -/
def coeff (k : Wave) : Table → ℚ
  | [] => 0
  | e :: l => (if e.1 = k then e.2 else 0) + coeff k l

theorem toTrig_cons (e : Wave × ℚ) (l : Table) :
    toTrig (e :: l) = Finsupp.single e.1 e.2 + toTrig l := by
  simp [toTrig]

theorem toTrig_append (l m : Table) : toTrig (l ++ m) = toTrig l + toTrig m := by
  simp [toTrig]

/-- The polynomial's coefficient is the table's. -/
theorem toTrig_apply (l : Table) (k : Wave) : toTrig l k = coeff k l := by
  induction l with
  | nil => rfl
  | cons e l ih => rw [toTrig_cons, Finsupp.add_apply, ih, coeff, Finsupp.single_apply]

/-- Add `a` to the entry at `k`, or append one. -/
def insert (k : Wave) (a : ℚ) : Table → Table
  | [] => [(k, a)]
  | e :: l => if e.1 = k then (k, e.2 + a) :: l else e :: insert k a l

theorem toTrig_insert (k : Wave) (a : ℚ) (l : Table) :
    toTrig (insert k a l) = Finsupp.single k a + toTrig l := by
  induction l with
  | nil => simp [insert, toTrig]
  | cons e l ih =>
      simp only [insert]
      split_ifs with h
      · rw [toTrig_cons, toTrig_cons, ← h, Finsupp.single_add]
        abel
      · rw [toTrig_cons, ih, toTrig_cons]
        abel

/-- Merge duplicate modes. -/
def normalize (l : Table) : Table := l.foldr (fun e acc => insert e.1 e.2 acc) []

theorem toTrig_normalize (l : Table) : toTrig (normalize l) = toTrig l := by
  induction l with
  | nil => rfl
  | cons e l ih => rw [normalize, List.foldr_cons, toTrig_insert, ← normalize, ih, toTrig_cons]

def smul (c : ℚ) (l : Table) : Table := l.map fun e => (e.1, c * e.2)

theorem toTrig_smul (c : ℚ) (l : Table) : toTrig (smul c l) = c • toTrig l := by
  induction l with
  | nil => simp [smul, toTrig]
  | cons e l ih => rw [smul, List.map_cons, toTrig_cons, ← smul, ih, toTrig_cons, smul_add,
      Finsupp.smul_single, smul_eq_mul]

def laplacian (l : Table) : Table := l.map fun e => (e.1, -(lam e.1 : ℚ) * e.2)

theorem toTrig_laplacian (l : Table) : toTrig (laplacian l) = Torus.laplacian (toTrig l) := by
  induction l with
  | nil => simp [laplacian, toTrig, Torus.laplacian_zero]
  | cons e l ih => rw [laplacian, List.map_cons, toTrig_cons, ← laplacian, ih, toTrig_cons,
      Torus.laplacian_add, Torus.laplacian_single]

/-- The transport of two tables: every pair of entries lands on the sum of
their modes with the coupling, then duplicates are merged. -/
def transport (l m : Table) : Table :=
  normalize (l.flatMap fun e => m.map fun f => (e.1 + f.1, coupling e.1 f.1 * e.2 * f.2))

theorem toTrig_transport_single (e : Wave × ℚ) (m : Table) :
    toTrig (m.map fun f => (e.1 + f.1, coupling e.1 f.1 * e.2 * f.2)) =
      Torus.transport (Finsupp.single e.1 e.2) (toTrig m) := by
  induction m with
  | nil => simp [toTrig, Torus.transport_zero_right]
  | cons f m ih => rw [List.map_cons, toTrig_cons, ih, toTrig_cons, Torus.transport_add_right,
      Torus.transport_single_single]

theorem toTrig_transport (l m : Table) :
    toTrig (transport l m) = Torus.transport (toTrig l) (toTrig m) := by
  rw [transport, toTrig_normalize]
  induction l with
  | nil => simp [toTrig, Torus.transport_zero_left]
  | cons e l ih => rw [List.flatMap_cons, toTrig_append, ih, toTrig_transport_single, toTrig_cons,
      Torus.transport_add_left]

/-- The sum of the absolute entries: an upper bound for the ℓ¹ norm of the
polynomial the table stands for, computable; exact when the modes are distinct. -/
def absSum : Table → ℚ
  | [] => 0
  | e :: l => |e.2| + absSum l

theorem l1_le_absSum (l : Table) : l1 (toTrig l) ≤ absSum l := by
  induction l with
  | nil => simp [toTrig, l1, absSum]
  | cons e l ih =>
      rw [toTrig_cons, absSum]
      exact (l1_add_le _ _).trans (add_le_add (l1_single_le _ _) ih)

/-- The modes of a table's polynomial are among the table's modes. -/
theorem sizeLE_toTrig {K : ℕ} {l : Table} (h : ∀ e ∈ l, size e.1 ≤ K) : SizeLE K (toTrig l) := by
  induction l with
  | nil => simpa [toTrig] using sizeLE_zero K
  | cons e l ih =>
      rw [toTrig_cons]
      refine sizeLE_add (fun k hk => ?_) (ih fun f hf => h f (List.mem_cons_of_mem e hf))
      have := Finsupp.support_single_subset hk
      rw [Finset.mem_singleton] at this
      rw [this]
      exact h e List.mem_cons_self

end Table

end Gimle.Asgard.Streams.Torus

namespace Gimle.Asgard.Streams.NS

open Torus

/-! ## The Picard iteration on tables -/

open Table (toTrig toTrig_apply toTrig_append toTrig_smul toTrig_laplacian toTrig_transport)

/-- A finite sequence of tables, one per `t`-degree. -/
abbrev Seq := List Table

/-- The table at degree `n`, empty beyond the sequence. -/
def Seq.get (w : Seq) (n : ℕ) : Table := w.getD n []

/-- The right-hand side `ν Δ ω_n − Σ_{m ≤ n} transport ω_m ω_{n−m}` at every
degree of the sequence. -/
def rhsSeq (ν : ℚ) (w : Seq) : Seq :=
  (List.range w.length).map fun n => Table.normalize
    (Table.smul ν (Table.laplacian (w.get n)) ++
      Table.smul (-1) ((List.range (n + 1)).flatMap fun m => Table.transport (w.get m) (w.get (n - m))))

/-- OGF integration from the initial table: degree `n + 1` is `a_n / (n + 1)`. -/
def integralSeq (a : Seq) (b₀ : Table) : Seq :=
  b₀ :: (List.range a.length).map fun (n : ℕ) => Table.smul ((n : ℚ) + 1)⁻¹ (a.get n)

/-- The `n`-th Picard iterate as a sequence of `n + 1` tables, computable. -/
def picard (ν : ℚ) (b₀ : Table) : ℕ → Seq
  | 0 => [b₀]
  | n + 1 => integralSeq (rhsSeq ν (picard ν b₀ n)) b₀

theorem rhsSeq_length (ν : ℚ) (w : Seq) : (rhsSeq ν w).length = w.length := by
  simp [rhsSeq]

theorem integralSeq_length (a : Seq) (b₀ : Table) : (integralSeq a b₀).length = a.length + 1 := by
  simp [integralSeq]

theorem picard_length (ν : ℚ) (b₀ : Table) (n : ℕ) : (picard ν b₀ n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [picard, integralSeq_length, rhsSeq_length, ih]

theorem get_map_range {f : ℕ → Table} {L n : ℕ} (h : n < L) :
    Seq.get ((List.range L).map f) n = f n := by
  simp [Seq.get, List.getD_eq_getElem?_getD, h]

theorem rhsSeq_get (ν : ℚ) (w : Seq) {n : ℕ} (h : n < w.length) :
    (rhsSeq ν w).get n = Table.normalize (Table.smul ν (Table.laplacian (w.get n)) ++
      Table.smul (-1) ((List.range (n + 1)).flatMap fun m => Table.transport (w.get m) (w.get (n - m)))) := by
  rw [rhsSeq, get_map_range h]

theorem integralSeq_get_zero (a : Seq) (b₀ : Table) : (integralSeq a b₀).get 0 = b₀ := rfl

theorem integralSeq_get_succ (a : Seq) (b₀ : Table) {n : ℕ} (h : n < a.length) :
    (integralSeq a b₀).get (n + 1) = Table.smul ((n : ℚ) + 1)⁻¹ (a.get n) := by
  simp only [integralSeq, Seq.get, List.getD_cons_succ]
  exact get_map_range h

theorem toTrig_flatMap_transport (w : Seq) (ω : TrigStream) (n : ℕ)
    (h : ∀ m ≤ n, toTrig (w.get m) = ω m) :
    toTrig ((List.range (n + 1)).flatMap fun m => Table.transport (w.get m) (w.get (n - m))) =
      ∑ m ∈ Finset.range (n + 1), Torus.transport (ω m) (ω (n - m)) := by
  have : ∀ L ≤ n + 1, toTrig ((List.range L).flatMap fun m => Table.transport (w.get m) (w.get (n - m))) =
      ∑ m ∈ Finset.range L, Torus.transport (ω m) (ω (n - m)) := by
    intro L hL
    induction L with
    | zero => simp [toTrig]
    | succ L ih =>
        rw [List.range_succ, List.flatMap_append, toTrig_append, ih (by omega),
          Finset.sum_range_succ, List.flatMap_singleton, toTrig_transport, h L (by omega),
          h (n - L) (by omega)]
  exact this (n + 1) le_rfl

/-- The sequence mirrors the Picard iterate at every degree it holds. -/
theorem toTrig_picard (ν : ℚ) (b₀ : Table) (b : TrigStream) (hb : toTrig b₀ = b 0) (n : ℕ) :
    ∀ m ≤ n, toTrig ((picard ν b₀ n).get m) =
      (TrigStream.trigAxis .ogf).approx (rhs .ogf ν) b n m := by
  induction n with
  | zero =>
      intro m hm
      rw [Nat.le_zero.mp hm]
      simpa [picard, Seq.get] using hb
  | succ n ih =>
      intro m hm
      rw [picard, Causal.Axis.approx_succ, TrigStream.trigAxis_integral]
      cases m with
      | zero => rw [integralSeq_get_zero, hb]; simp
      | succ m =>
          have lt : m < (rhsSeq ν (picard ν b₀ n)).length := by
            rw [rhsSeq_length, picard_length]; omega
          have lt' : m < (picard ν b₀ n).length := by rw [picard_length]; omega
          rw [integralSeq_get_succ _ _ lt, toTrig_smul, rhsSeq_get _ _ lt', Table.toTrig_normalize,
            toTrig_append,
            toTrig_smul, toTrig_smul, toTrig_laplacian, ih m (by omega),
            toTrig_flatMap_transport _ _ _ fun j hj => ih j (by omega),
            TrigStream.integral_ogf_succ, rhs, TrigStream.convolve_ogf_apply]
          congr 1
          rw [neg_one_smul, sub_eq_add_neg]

/-- **The stream's coefficient table.** At `t`-degree `n`, the OGF vorticity
stream from the initial table is the polynomial the `n`-th sequence holds. -/
theorem stream_eq_table (ν : ℚ) (b₀ : Table) (b : TrigStream) (hb : toTrig b₀ = b 0) (n : ℕ) :
    stream .ogf ν b n = toTrig ((picard ν b₀ n).get n) := by
  rw [stream_apply, toTrig_picard ν b₀ b hb n n le_rfl]

/-- The coefficient at mode `k` is the rational the kernel computes. -/
theorem stream_coeff (ν : ℚ) (b₀ : Table) (b : TrigStream) (hb : toTrig b₀ = b 0) (n : ℕ)
    (k : Wave) : stream .ogf ν b n k = Table.coeff k ((picard ν b₀ n).get n) := by
  rw [stream_eq_table ν b₀ b hb n, toTrig_apply]

#print axioms toTrig_transport
#print axioms Torus.Table.l1_le_absSum
#print axioms Torus.Table.sizeLE_toTrig
#print axioms stream_eq_table
#print axioms stream_coeff
end Gimle.Asgard.Streams.NS
