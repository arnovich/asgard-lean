import Gimle.Asgard.Streams.ExpPolyTable
import Gimle.Asgard.Streams.Mild
import Gimle.Asgard.Streams.VorticityTable

/-! Computable Wild coefficients, with an exact bridge to the circuit's output. -/
namespace Gimle.Asgard.Streams.Mild

open Torus

/-- Sparse Fourier entries with sparse exact time-dependent coefficients. -/
abbrev Table := List (Wave × ExpPoly.Table)

namespace Table

noncomputable def toMild (l : Table) : MildPoly :=
  (l.map fun e => Finsupp.single e.1 e.2.toExp).sum

@[simp] theorem toMild_nil : toMild [] = 0 := rfl
@[simp] theorem toMild_cons (e : Wave × ExpPoly.Table) (l : Table) :
    toMild (e :: l) = Finsupp.single e.1 e.2.toExp + toMild l := by simp [toMild]

theorem toMild_append (l m : Table) : toMild (l ++ m) = toMild l + toMild m := by
  simp [toMild]

/-- Merge repeated Fourier entries, normalizing their exact time coefficients. -/
def insert (k : Wave) (a : ExpPoly.Table) : Table → Table
  | [] => [(k, ExpPoly.Table.normalize a)]
  | e :: l => if e.1 = k then (k, ExpPoly.Table.normalize (e.2 ++ a)) :: l
    else e :: insert k a l

theorem toMild_insert (k : Wave) (a : ExpPoly.Table) (l : Table) :
    toMild (insert k a l) = Finsupp.single k a.toExp + toMild l := by
  induction l with
  | nil => simp [insert, ExpPoly.Table.toExp_normalize]
  | cons e l ih =>
      simp only [insert]
      split_ifs with h
      · rw [toMild_cons, toMild_cons, ExpPoly.Table.toExp_normalize,
          ExpPoly.Table.toExp_append, ← h, Finsupp.single_add]
        abel
      · rw [toMild_cons, ih, toMild_cons]
        abel

private theorem toMild_filter_nonempty (l : Table) :
    toMild (l.filter fun e => !e.2.isEmpty) = toMild l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      rcases e with ⟨k, a⟩
      cases a <;> simp [ih]

def normalize (l : Table) : Table :=
  (l.foldr (fun e acc => insert e.1 e.2 acc) []).filter fun e => !e.2.isEmpty

theorem toMild_normalize (l : Table) : toMild (normalize l) = toMild l := by
  unfold normalize
  rw [toMild_filter_nonempty]
  induction l with
  | nil => rfl
  | cons e l ih => rw [List.foldr_cons, toMild_insert, ih, toMild_cons]

def smul (a : ℚ) (l : Table) : Table := l.map fun e => (e.1, ExpPoly.Table.smul a e.2)

theorem toMild_smul (a : ℚ) (l : Table) : toMild (smul a l) = a • toMild l := by
  induction l with
  | nil => simp [smul]
  | cons e l ih => rw [smul, List.map_cons, toMild_cons, ← smul, ih, toMild_cons,
      smul_add, Finsupp.smul_single, ExpPoly.Table.toExp_smul]

def heat (l : Table) : Table := l.map fun e => (e.1, ExpPoly.Table.heat (heatRate e.1) e.2)

theorem toMild_heat (l : Table) : toMild (heat l) = Mild.heat (toMild l) := by
  induction l with
  | nil => simp [heat]
  | cons e l ih => rw [heat, List.map_cons, toMild_cons, ← heat, ih, toMild_cons,
      Mild.heat_add, Mild.heat_single, ExpPoly.Table.toExp_heat]

def duhamel (ν : ℚ) (l : Table) : Table :=
  l.map fun e => (e.1, ExpPoly.Table.duhamel ν (heatRate e.1) e.2)

theorem toMild_duhamel (ν : ℚ) (l : Table) : toMild (duhamel ν l) = Mild.duhamel ν (toMild l) := by
  induction l with
  | nil => simp [duhamel]
  | cons e l ih => rw [duhamel, List.map_cons, toMild_cons, ← duhamel, ih, toMild_cons,
      Mild.duhamel_add, Mild.duhamel_single, ExpPoly.Table.toExp_duhamel]

def transport (l m : Table) : Table := normalize (l.flatMap fun e => m.map fun f =>
  (e.1 + f.1, ExpPoly.Table.smul (coupling e.1 f.1) (ExpPoly.Table.mul e.2 f.2)))

private theorem toMild_transport_single (e : Wave × ExpPoly.Table) (m : Table) :
    toMild (m.map fun f =>
      (e.1 + f.1, ExpPoly.Table.smul (coupling e.1 f.1) (ExpPoly.Table.mul e.2 f.2))) =
      Mild.transport (Finsupp.single e.1 e.2.toExp) (toMild m) := by
  induction m with
  | nil => simp [Mild.transport_zero_right]
  | cons f m ih =>
      rw [List.map_cons, toMild_cons, ih, toMild_cons, Mild.transport_add_right,
        Mild.transport_single_single, ExpPoly.Table.toExp_smul, ExpPoly.Table.toExp_mul]
      simp [Algebra.smul_def, mul_assoc]

theorem toMild_transport (l m : Table) : toMild (transport l m) = Mild.transport (toMild l) (toMild m) := by
  unfold transport
  rw [toMild_normalize]
  induction l with
  | nil => simp [Mild.transport_zero_left]
  | cons e l ih => rw [List.flatMap_cons, toMild_append, toMild_transport_single, ih,
      toMild_cons, Mild.transport_add_left]

/-- Constant-time initial data; the heat operator supplies the mode decay. -/
def embed (l : Torus.Table) : Table := l.map fun e => (e.1, [((0, 0), e.2)])

theorem toMild_embed (l : Torus.Table) : toMild (embed l) = Mild.embed l.toTrig := by
  induction l with
  | nil => apply Finsupp.ext; intro k; simp [embed, Torus.Table.toTrig]
  | cons e l ih =>
      rw [embed, List.map_cons, toMild_cons, ← embed, ih, Torus.Table.toTrig_cons]
      apply Finsupp.ext
      intro k
      simp only [Finsupp.add_apply, Mild.embed_apply, map_add, Finsupp.single_apply]
      by_cases h : e.1 = k <;> simp [h, ExpPoly.Table.term]

/-- Read a mode, summing every listed contribution to that mode. -/
def coeff (k : Wave) : Table → ExpPoly.Table
  | [] => []
  | e :: l => (if e.1 = k then e.2 else []) ++ coeff k l

theorem toMild_apply (l : Table) (k : Wave) : toMild l k = (coeff k l).toExp := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      rw [toMild_cons, Finsupp.add_apply, ih, coeff, ExpPoly.Table.toExp_append]
      by_cases h : e.1 = k <;> simp [h]

end Table
/-- A finite initial segment of interaction-degree tables. -/
abbrev Seq := List Table

def Seq.get (w : Seq) (n : ℕ) : Table := w.getD n []

/-- Integrate the quadratic forcing at each degree already available. -/
def rhsSeq (ν : ℚ) (w : Seq) : Seq :=
  (List.range w.length).map fun n => Table.smul (-1) (Table.duhamel ν
    (Table.normalize ((List.range (n + 1)).flatMap fun m =>
      Table.transport (w.get m) (w.get (n - m)))))

/-- The n-th Picard table segment has n+1 exact coefficients. -/
def picard (ν : ℚ) (b : Table) : ℕ → Seq
  | 0 => [Table.heat b]
  | n + 1 => Table.heat b :: rhsSeq ν (picard ν b n)

theorem rhsSeq_length (ν : ℚ) (w : Seq) : (rhsSeq ν w).length = w.length := by simp [rhsSeq]

theorem picard_length (ν : ℚ) (b : Table) (n : ℕ) : (picard ν b n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [picard, rhsSeq_length, ih]

theorem rhsSeq_get (ν : ℚ) (w : Seq) {n : ℕ} (h : n < w.length) :
    (rhsSeq ν w).get n = Table.smul (-1) (Table.duhamel ν
      (Table.normalize ((List.range (n + 1)).flatMap fun m =>
        Table.transport (w.get m) (w.get (n - m))))) := by
  simp [rhsSeq, Seq.get, List.getD_eq_getElem?_getD, h]

private theorem toMild_flatMap_transport (w : Seq) (ω : Stream) (n : ℕ)
    (h : ∀ m ≤ n, (w.get m).toMild = ω m) :
    Table.toMild ((List.range (n + 1)).flatMap fun m => Table.transport (w.get m) (w.get (n - m))) =
      ∑ m ∈ Finset.range (n + 1), transport (ω m) (ω (n - m)) := by
  have aux : ∀ L ≤ n + 1,
      Table.toMild ((List.range L).flatMap fun m => Table.transport (w.get m) (w.get (n - m))) =
        ∑ m ∈ Finset.range L, transport (ω m) (ω (n - m)) := by
    intro L hL
    induction L with
    | zero => simp
    | succ L ih =>
        rw [List.range_succ, List.flatMap_append, Table.toMild_append, ih (by omega),
          Finset.sum_range_succ, List.flatMap_singleton, Table.toMild_transport,
          h L (by omega), h (n - L) (by omega)]
  exact aux (n + 1) le_rfl

/-- Finite table iteration agrees with every coefficient of the causal iterate it holds. -/
theorem toMild_picard (ν : ℚ) (b₀ : Table) (b : Stream) (hb : b₀.toMild = b 0) (n : ℕ) :
    ∀ m ≤ n, ((picard ν b₀ n).get m).toMild =
      (shiftAxis MildPoly).approx (rhs ν) (fun k => heat (b k)) n m := by
  induction n with
  | zero =>
      intro m hm
      rw [Nat.le_zero.mp hm]
      simpa [picard, Seq.get, Table.toMild_heat] using congrArg heat hb
  | succ n ih =>
      intro m hm
      rw [picard, Causal.Axis.approx_succ]
      cases m with
      | zero =>
          change (Table.heat b₀).toMild = heat (b 0)
          rw [Table.toMild_heat, hb]
      | succ m =>
          have lt : m < (picard ν b₀ n).length := by rw [picard_length]; omega
          change ((rhsSeq ν (picard ν b₀ n)).get m).toMild = _
          rw [rhsSeq_get _ _ lt, Table.toMild_smul, Table.toMild_duhamel,
            Table.toMild_normalize, toMild_flatMap_transport _ _ _ (fun j hj => ih j (by omega))]
          change (-1 : ℚ) • duhamel ν _ = -duhamel ν _
          apply Finsupp.ext
          intro k
          simp

/-- Exact interaction coefficients computed by the kernel, without trusted simulation. -/
theorem stream_eq_table (ν : ℚ) (b₀ : Table) (b : Stream) (hb : b₀.toMild = b 0) (n : ℕ) :
    wild ν b n = ((picard ν b₀ n).get n).toMild :=
  (toMild_picard ν b₀ b hb n n le_rfl).symm

/-- An exact scalar coefficient read from a finite table. -/
theorem stream_coeff (ν : ℚ) (b₀ : Table) (b : Stream) (hb : b₀.toMild = b 0)
    (n : ℕ) (k : Wave) (rate degree : ℕ) :
    (((wild ν b n k).coeff rate).coeff degree) =
      ExpPoly.Table.coeff rate degree (Table.coeff k ((picard ν b₀ n).get n)) := by
  rw [stream_eq_table ν b₀ b hb n, Table.toMild_apply, ExpPoly.Table.toExp_coeff]

#print axioms Table.toMild_transport
#print axioms Table.toMild_duhamel
#print axioms stream_eq_table

end Gimle.Asgard.Streams.Mild
