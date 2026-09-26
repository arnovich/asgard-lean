import Gimle.Asgard.Streams.Laws
import Gimle.Asgard.Compile.Polynomial

/-! Lowering finite coefficient observations of stream circuits.

A stream circuit maps whole infinite coefficient streams. A finite polynomial
certificate can speak about it only through finitely many coefficients, and
only if a theorem ties those coefficients to the original circuit. This module
is that tie.

`lower` computes, for one output coefficient of a stream circuit, an exact
polynomial `Term` in finitely many *input* coefficients — its dependencies —
and `lower_correct` proves the output coefficient equals that polynomial
evaluated on the input's coefficients, for every input stream. Derivatives read
one coefficient past the observed one (a halo); products read every split of
the index along every axis; integrals read the boundary slot at degree zero.
Composition substitutes the first stage's terms into the second's, so
requirements propagate backwards through windows of any shape.

Series substitution is rejected, anywhere in the circuit, even where its output
is later discarded: the lowering never erases Asgard's strict domain.

Degrees are plain functions `Fin d → ℕ` so that the lowering computes; they
meet Asgard's finitely supported `Index d` only in the semantics.
-/

namespace Gimle.Asgard.Streams.Lowering

open Gimle.Asgard.Streams

/-- A multi-index as a plain function, so lowering computes. -/
abbrev Degrees (d : Nat) := Fin d → ℕ

/-- Degree vectors compare as lists, so equality reduces in the kernel; the
generic instance for functions on a finite type does not. -/
scoped instance (priority := high) Degrees.decEq {d : Nat} : DecidableEq (Degrees d) :=
  fun a b => decidable_of_iff (List.ofFn a = List.ofFn b) List.ofFn_inj

/-- The finitely supported index a degree vector names. -/
noncomputable def Degrees.toIndex {d : Nat} (degrees : Degrees d) : Index d :=
  Finsupp.equivFunOnFinite.symm degrees

@[simp] theorem Degrees.toIndex_apply {d : Nat} (degrees : Degrees d) (i : Fin d) :
    degrees.toIndex i = degrees i := rfl

theorem Degrees.toIndex_injective {d : Nat} : Function.Injective (@Degrees.toIndex d) :=
  Finsupp.equivFunOnFinite.symm.injective

/-- One input or output coefficient: a port and a degree vector. -/
structure Slot (n d : Nat) where
  port : Fin n
  degrees : Degrees d

/-- Slots compare by port value and degrees. Written out rather than derived:
the derived instance casts along the port equality, which blocks the kernel. -/
instance {n d : Nat} : DecidableEq (Slot n d) := fun a b =>
  decidable_of_iff (a.port.val = b.port.val ∧ a.degrees = b.degrees) (by
    cases a; cases b
    constructor
    · rintro ⟨port, degrees⟩
      simp_all [Fin.ext_iff]
    · intro same
      cases same
      exact ⟨rfl, rfl⟩)

/-- An exact polynomial in coefficients. -/
inductive Term (n d : Nat) where
  | slot (s : Slot n d)
  | const (q : ℚ)
  | add (a b : Term n d)
  | mul (a b : Term n d)

/-- Structural equality of terms, as a Boolean. -/
def Term.beq {n d : Nat} : Term n d → Term n d → Bool
  | .slot s, .slot t => decide (s = t)
  | .const q, .const r => decide (q = r)
  | .add a b, .add c e => a.beq c && b.beq e
  | .mul a b, .mul c e => a.beq c && b.beq e
  | _, _ => false

theorem Term.beq_iff {n d : Nat} : (a b : Term n d) → (a.beq b = true ↔ a = b)
  | .slot s, .slot t => by simp [beq]
  | .const q, .const r => by simp [beq]
  | .add a b, .add c e => by simp [beq, beq_iff a c, beq_iff b e]
  | .mul a b, .mul c e => by simp [beq, beq_iff a c, beq_iff b e]
  | .slot _, .const _ | .slot _, .add _ _ | .slot _, .mul _ _
  | .const _, .slot _ | .const _, .add _ _ | .const _, .mul _ _
  | .add _ _, .slot _ | .add _ _, .const _ | .add _ _, .mul _ _
  | .mul _ _, .slot _ | .mul _ _, .const _ | .mul _ _, .add _ _ => by simp [beq]

/-- Terms compare structurally, by `Term.beq`, so equality reduces in the kernel. -/
instance {n d : Nat} : DecidableEq (Term n d) := fun a b =>
  decidable_of_iff _ (Term.beq_iff a b)

namespace Term

variable {n d : Nat}

/-- The value of a term on the coefficients of a stream point. -/
noncomputable def eval (x : StreamPoint d n) : Term n d → ℚ
  | slot s => x s.port s.degrees.toIndex
  | const q => q
  | add a b => a.eval x + b.eval x
  | mul a b => a.eval x * b.eval x

/-- The sum of a list of terms. -/
def sum : List (Term n d) → Term n d
  | [] => const 0
  | t :: ts => add t (sum ts)

@[simp] theorem eval_sum (x : StreamPoint d n) (terms : List (Term n d)) :
    (sum terms).eval x = (terms.map (eval x)).sum := by
  induction terms with
  | nil => rfl
  | cons t ts ih => simp [sum, eval, ih]

/-- The number of nodes, for resource limits. -/
def size : Term n d → Nat
  | slot _ | const _ => 1
  | add a b | mul a b => a.size + b.size + 1

/-- The coefficients a term reads, possibly with repetition. -/
def slots : Term n d → List (Slot n d)
  | slot s => [s]
  | const _ => []
  | add a b | mul a b => a.slots ++ b.slots

/-- A term depends only on the coefficients it reads. -/
theorem eval_congr {x y : StreamPoint d n} (t : Term n d)
    (same : ∀ s ∈ t.slots, x s.port s.degrees.toIndex = y s.port s.degrees.toIndex) :
    t.eval x = t.eval y := by
  induction t with
  | slot s => exact same s (by simp [slots])
  | const q => rfl
  | add a b ha hb =>
      simp only [eval]
      rw [ha fun s h => same s (by simp [slots, h]),
        hb fun s h => same s (by simp [slots, h])]
  | mul a b ha hb =>
      simp only [eval]
      rw [ha fun s h => same s (by simp [slots, h]),
        hb fun s h => same s (by simp [slots, h])]

end Term

/-! ### Splitting an index -/

/-- Every degree vector coordinatewise at most `k`, in a fixed order. -/
def grid : (d : Nat) → Degrees d → List (Degrees d)
  | 0, _ => [Fin.elim0]
  | d + 1, k => (List.range (k 0 + 1)).flatMap fun a =>
      (grid d (Fin.tail k)).map (Fin.cons a)

theorem mem_grid : {d : Nat} → (k a : Degrees d) → (a ∈ grid d k ↔ ∀ i, a i ≤ k i)
  | 0, k, a => by simp [grid]; funext i; exact Fin.elim0 i
  | d + 1, k, a => by
      simp only [grid, List.mem_flatMap, List.mem_range, List.mem_map, mem_grid]
      constructor
      · rintro ⟨head, below, tail, tail_below, rfl⟩ i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using Nat.lt_succ_iff.mp below
        · simpa [Fin.tail] using tail_below j
      · intro below
        refine ⟨a 0, Nat.lt_succ_of_le (below 0), Fin.tail a, fun j => below j.succ, ?_⟩
        exact Fin.cons_self_tail a

theorem grid_nodup : {d : Nat} → (k : Degrees d) → (grid d k).Nodup
  | 0, _ => by simp [grid]
  | d + 1, k => by
      simp only [grid]
      refine List.nodup_flatMap.mpr ⟨fun a _ => (grid_nodup (Fin.tail k)).map
        (fun x y same => by simpa using congrArg Fin.tail same), ?_⟩
      refine List.nodup_range.pairwise_of_forall_ne (fun a _ b _ different => ?_)
      rw [Function.onFun, List.disjoint_left]
      simp only [List.mem_map]
      rintro _ ⟨x, _, rfl⟩ ⟨y, _, same⟩
      exact different (by simpa using (congrFun same 0).symm)

/-- A sum over the antidiagonal of an index is a sum over the grid below it. -/
theorem sum_antidiagonal {d : Nat} (k : Degrees d) (f : Index d → Index d → ℚ) :
    ∑ p ∈ Finset.antidiagonal k.toIndex, f p.1 p.2 =
      ((grid d k).map fun a => f a.toIndex (k - a).toIndex).sum := by
  rw [← List.sum_toFinset _ (grid_nodup k)]
  symm
  refine Finset.sum_nbij' (fun a => (a.toIndex, (k - a).toIndex)) (fun p => ⇑p.1)
    ?_ ?_ ?_ ?_ ?_
  · intro a member
    have below := (mem_grid k a).mp (List.mem_toFinset.mp member)
    rw [Finset.mem_antidiagonal]
    ext i
    simp [Nat.add_sub_cancel' (below i)]
  · intro p member
    rw [Finset.mem_antidiagonal] at member
    rw [List.mem_toFinset, mem_grid]
    intro i
    have := congrArg (fun q => q i) member
    simp at this
    omega
  · intro a _
    rfl
  · intro p member
    rw [Finset.mem_antidiagonal] at member
    have second : (k - ⇑p.1) = ⇑p.2 := by
      funext i
      have := congrArg (fun q => q i) member
      simp at this
      simp
      omega
    ext i <;> simp [second]
  · intro a _
    rfl

/-! ### Coefficients of the primitives -/

namespace Degrees

variable {d : Nat}

/-- One axis moved to a given degree. A plain `if` rather than a dependent
update, so it reduces in the kernel. -/
def set (k : Degrees d) (axis : Fin d) (degree : ℕ) : Degrees d :=
  fun i => if i = axis then degree else k i

/-- The index with one axis moved to a given degree. -/
theorem toIndex_update (k : Degrees d) (axis : Fin d) (degree : ℕ) :
    (k.toIndex).update axis degree = (k.set axis degree).toIndex := by
  ext i
  by_cases same : i = axis
  · subst same; simp [set]
  · simp [Finsupp.update_apply, same, set]

/-- `α₁!⋯α_d!`, computably. -/
def factorial (k : Degrees d) : ℚ := ∏ i, ((k i).factorial : ℚ)

theorem factorial_toIndex (k : Degrees d) : Streams.factorial k.toIndex = k.factorial := rfl

theorem toIndex_eq_zero (k : Degrees d) : k.toIndex = 0 ↔ k = 0 := by
  constructor
  · intro zero; funext i; simpa using congrArg (· i) zero
  · rintro rfl; ext i; simp

theorem toIndex_eq_single (k : Degrees d) (axis : Fin d) :
    k.toIndex = Finsupp.single axis 1 ↔ k = Pi.single axis 1 := by
  constructor
  · intro same
    funext i
    have := congrArg (· i) same
    simp only [Degrees.toIndex_apply] at this
    rw [this]
    by_cases h : i = axis
    · subst h; simp
    · simp [h]
  · rintro rfl
    ext i
    by_cases h : i = axis
    · subst h; simp
    · simp [h]

end Degrees

/-- The raw coefficient of a constant at a degree vector. -/
def constantCoefficient {d : Nat} (q : ℚ) (k : Degrees d) : ℚ :=
  if k = 0 then q else 0

theorem constant_coefficient {d : Nat} (basis : Basis) (q : ℚ) (k : Degrees d) :
    Streams.constant basis q k.toIndex = constantCoefficient q k := by
  have plain : (MvPowerSeries.C q : Stream d) k.toIndex = constantCoefficient q k := by
    change MvPowerSeries.coeff k.toIndex (MvPowerSeries.C q) = _
    rw [MvPowerSeries.coeff_C]
    simp [constantCoefficient, Degrees.toIndex_eq_zero]
  cases basis with
  | ogf => exact plain
  | egf =>
      change Streams.factorial k.toIndex * _ = _
      rw [plain]
      by_cases zero : k = 0
      · subst zero; simp [constantCoefficient, Streams.factorial]
      · simp [constantCoefficient, zero]

/-- The raw coefficient of an axis variable at a degree vector. -/
def variableCoefficient {d : Nat} (axis : Fin d) (k : Degrees d) : ℚ :=
  if k = Pi.single axis 1 then 1 else 0

theorem axisVariable_coefficient {d : Nat} (basis : Basis) (axis : Fin d) (k : Degrees d) :
    Streams.axisVariable basis axis k.toIndex = variableCoefficient axis k := by
  have plain : (MvPowerSeries.X axis : Stream d) k.toIndex = variableCoefficient axis k := by
    change MvPowerSeries.coeff k.toIndex (MvPowerSeries.X axis) = _
    rw [MvPowerSeries.coeff_X]
    simp [variableCoefficient, Degrees.toIndex_eq_single]
  cases basis with
  | ogf => exact plain
  | egf =>
      change Streams.factorial k.toIndex * _ = _
      rw [plain]
      by_cases one : k = Pi.single axis 1
      · subst one
        simp [variableCoefficient, Streams.factorial, Pi.single_apply]
        apply Finset.prod_eq_one
        intro i _
        by_cases h : i = axis <;> simp [h]
      · simp [variableCoefficient, one]

/-- The factor a derivative applies to the next coefficient along its axis. -/
def derivativeFactor {d : Nat} (basis : Basis) (axis : Fin d) (k : Degrees d) : ℚ :=
  match basis with
  | .ogf => (k axis + 1 : ℚ)
  | .egf => 1

theorem derivative_coefficient {d : Nat} (basis : Basis) (axis : Fin d) (a : Stream d)
    (k : Degrees d) :
    Streams.derivative basis axis a k.toIndex =
      derivativeFactor basis axis k * a ((k.set axis (k axis + 1)).toIndex) := by
  cases basis <;> simp [Streams.derivative, derivativeFactor, Degrees.toIndex_update]

/-- The factor an integral applies to the previous coefficient along its axis. -/
def integralFactor {d : Nat} (basis : Basis) (axis : Fin d) (k : Degrees d) : ℚ :=
  match basis with
  | .ogf => 1 / (k axis : ℚ)
  | .egf => 1

theorem integral_coefficient {d : Nat} (basis : Basis) (axis : Fin d) (a boundary : Stream d)
    (k : Degrees d) :
    Streams.integral basis axis a boundary k.toIndex =
      if k axis = 0 then boundary k.toIndex else
        integralFactor basis axis k * a ((k.set axis (k axis - 1)).toIndex) := by
  cases basis <;> by_cases zero : k axis = 0 <;>
    simp [Streams.integral, integralFactor, zero, Degrees.toIndex_update, div_eq_inv_mul]

/-- The weight of one split `k = g + (k − g)` in a product. -/
def productWeight {d : Nat} (basis : Basis) (k g : Degrees d) : ℚ :=
  match basis with
  | .ogf => 1
  | .egf => k.factorial / (g.factorial * (k - g).factorial)

theorem product_coefficient {d : Nat} (basis : Basis) (a b : Stream d) (k : Degrees d) :
    Streams.product basis a b k.toIndex =
      ((grid d k).map fun g => productWeight basis k g * a g.toIndex * b (k - g).toIndex).sum := by
  have split (u v : Stream d) :
      (u * v : Stream d) k.toIndex =
        ((grid d k).map fun g => u g.toIndex * v (k - g).toIndex).sum := by
    change MvPowerSeries.coeff k.toIndex (u * v) = _
    rw [MvPowerSeries.coeff_mul]
    exact sum_antidiagonal k (fun p q => u p * v q)
  cases basis with
  | ogf =>
      change (decode .ogf a * decode .ogf b) k.toIndex = _
      simp [decode, split, productWeight]
  | egf =>
      change Streams.factorial k.toIndex * (decode .egf a * decode .egf b) k.toIndex = _
      rw [split, ← List.sum_map_mul_left, Degrees.factorial_toIndex]
      congr 1
      apply List.map_congr_left
      intro g _
      simp only [decode, productWeight, Degrees.factorial_toIndex]
      have gpos : g.factorial ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => by
        exact_mod_cast Nat.factorial_ne_zero (g i)
      have rpos : (k - g).factorial ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => by
        exact_mod_cast Nat.factorial_ne_zero ((k - g) i)
      field_simp

/-! ### Substitution -/

namespace Term

variable {n m d : Nat}

/-- Replace every slot by a term. -/
def bind (substitute : Slot m d → Term n d) : Term m d → Term n d
  | slot s => substitute s
  | const q => const q
  | add a b => add (bind substitute a) (bind substitute b)
  | mul a b => mul (bind substitute a) (bind substitute b)

/-- Substituting terms that evaluate to a point's coefficients evaluates at that
point. -/
theorem eval_bind (substitute : Slot m d → Term n d) (t : Term m d)
    (x : StreamPoint d n) (y : StreamPoint d m)
    (agree : ∀ s, (substitute s).eval x = y s.port s.degrees.toIndex) :
    (bind substitute t).eval x = t.eval y := by
  induction t with
  | slot s => exact agree s
  | const q => rfl
  | add a b ha hb => simp [bind, eval, ha, hb]
  | mul a b ha hb => simp [bind, eval, ha, hb]

/-- Rename ports. -/
def mapPorts (f : Fin m → Fin n) (t : Term m d) : Term n d :=
  bind (fun s => slot ⟨f s.port, s.degrees⟩) t

theorem eval_mapPorts (f : Fin m → Fin n) (t : Term m d) (x : StreamPoint d n) :
    (mapPorts f t).eval x = t.eval fun i => x (f i) :=
  eval_bind _ t x _ fun _ => rfl

end Term

/-! ### Lowering -/

variable {basis : Basis} {d : Nat}

/-- Whether a binary operation has a lowering: series substitution has none. -/
def lowerable : Binary d → Bool
  | .seriesCompose _ => false
  | _ => true

/-- Whether every constructor of a circuit has a lowering. Series substitution
has none, and is refused wherever it occurs, even in a branch whose output is
discarded. -/
def supported : {n m : Nat} → Circuit basis d n m → Bool
  | _, _, .route _ => true
  | _, _, .constant _ => true
  | _, _, .axisVariable _ => true
  | _, _, .unary _ => true
  | _, _, .binary op => lowerable op
  | _, _, .compose a b => supported a && supported b
  | _, _, .parallel a b => supported a && supported b

/-- The term for one output coefficient of a binary operation. -/
def lowerBinary (basis : Basis) : Binary d → Degrees d → Term 2 d
  | .add, k => .add (.slot ⟨0, k⟩) (.slot ⟨1, k⟩)
  | .product, k => Term.sum ((grid d k).map fun g =>
      .mul (.mul (.const (productWeight basis k g)) (.slot ⟨0, g⟩)) (.slot ⟨1, k - g⟩))
  | .integral axis, k =>
      if k axis = 0 then .slot ⟨1, k⟩ else
        .mul (.const (integralFactor basis axis k))
          (.slot ⟨0, k.set axis (k axis - 1)⟩)
  | .seriesCompose _, _ => .const 0

/-- The term for one output coefficient of a circuit, in its input coefficients. -/
def lowerRaw : {n m : Nat} → Circuit basis d n m → Fin m → Degrees d → Term n d
  | _, _, .route f, j, k => .slot ⟨f j, k⟩
  | _, _, .constant q, _, k => .const (constantCoefficient q k)
  | _, _, .axisVariable axis, _, k => .const (variableCoefficient axis k)
  | _, _, .unary (.derivative axis), _, k =>
      .mul (.const (derivativeFactor basis axis k))
        (.slot ⟨0, k.set axis (k axis + 1)⟩)
  | _, _, .binary op, _, k => lowerBinary basis op k
  | _, _, .compose a b, j, k => (lowerRaw b j k).bind fun s => lowerRaw a s.port s.degrees
  | _, _, .parallel (n := n) (k := p) a b, j, k =>
      Fin.addCases (motive := fun _ => Term (n + p) d)
        (fun j => (lowerRaw a j k).mapPorts (Fin.castAdd p))
        (fun j => (lowerRaw b j k).mapPorts (Fin.natAdd n)) j

/-- A supported circuit is defined everywhere: only series substitution has a
domain condition. -/
theorem supported_defined : {n m : Nat} → (c : Circuit basis d n m) → supported c = true →
    ∀ x, c.Defined x
  | _, _, .route _, _, _ | _, _, .constant _, _, _ | _, _, .axisVariable _, _, _
  | _, _, .unary _, _, _ => trivial
  | _, _, .binary op, ok, _ => by
      cases op <;> simp_all [supported, lowerable, Circuit.Defined, Binary.Domain]
  | _, _, .compose a b, ok, x => by
      simp only [supported, Bool.and_eq_true] at ok
      exact ⟨supported_defined a ok.1 x, supported_defined b ok.2 _⟩
  | _, _, .parallel a b, ok, x => by
      simp only [supported, Bool.and_eq_true] at ok
      exact ⟨supported_defined a ok.1 _, supported_defined b ok.2 _⟩

/-- **The lowering is exact.** For a supported circuit, every output coefficient
equals its lowered term evaluated on the input's coefficients. -/
theorem lowerRaw_correct : {n m : Nat} → (c : Circuit basis d n m) → supported c = true →
    ∀ (x : StreamPoint d n) (j : Fin m) (k : Degrees d),
      c.value x j k.toIndex = (lowerRaw c j k).eval x
  | _, _, .route f, _, x, j, k => rfl
  | _, _, .constant q, _, x, j, k => by
      rw [Subsingleton.elim j 0]
      exact constant_coefficient basis q k
  | _, _, .axisVariable axis, _, x, j, k => by
      rw [Subsingleton.elim j 0]
      exact axisVariable_coefficient basis axis k
  | _, _, .unary (.derivative axis), _, x, j, k => by
      rw [Subsingleton.elim j 0]
      exact derivative_coefficient basis axis (x 0) k
  | _, _, .binary op, ok, x, j, k => by
      rw [Subsingleton.elim j 0]
      cases op with
      | add => rfl
      | product =>
          change Streams.product basis (x 0) (x 1) k.toIndex = _
          rw [product_coefficient]
          simp [lowerRaw, lowerBinary, Term.eval, List.map_map, Function.comp_def]
      | integral axis =>
          change Streams.integral basis axis (x 0) (x 1) k.toIndex = _
          rw [integral_coefficient]
          by_cases zero : k axis = 0 <;> simp [lowerRaw, lowerBinary, zero, Term.eval]
      | seriesCompose _ => simp [supported, lowerable] at ok
  | _, _, .compose a b, ok, x, j, k => by
      simp only [supported, Bool.and_eq_true] at ok
      change b.value (a.value x) j k.toIndex = _
      rw [lowerRaw_correct b ok.2]
      exact (Term.eval_bind _ _ x _ fun s => (lowerRaw_correct a ok.1 x s.port s.degrees).symm).symm
  | _, _, .parallel (n := n) (k := p) a b, ok, x, j, k => by
      simp only [supported, Bool.and_eq_true] at ok
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · change append (a.value (left x)) (b.value (right x)) (Fin.castAdd _ i) k.toIndex = _
        simp only [append, Fin.addCases_left, lowerRaw, Term.eval_mapPorts]
        exact lowerRaw_correct a ok.1 _ i k
      · change append (a.value (left x)) (b.value (right x)) (Fin.natAdd _ i) k.toIndex = _
        simp only [append, Fin.addCases_right, lowerRaw, Term.eval_mapPorts]
        exact lowerRaw_correct b ok.2 _ i k

/-! ### Observation manifests -/

/-- A finite set of coefficients to observe: slots naming a port and a degree
vector, with the circuit's ordered axis IDs and port IDs alongside. The basis
is part of the type, so a manifest cannot be read in the other basis. -/
structure Manifest (basis : Basis) (n d : Nat) where
  axes : Fin d → String
  ports : Fin n → String
  slots : List (Slot n d)

namespace Manifest

variable {n : Nat}

/-- The coefficients a manifest names, read from a full stream point, exactly. -/
noncomputable def extract (manifest : Manifest basis n d) (x : StreamPoint d n) : List ℚ :=
  manifest.slots.map fun s => x s.port s.degrees.toIndex

/-- The rectangular window `degree < window` on one port, in grid order. A
window of size zero along any axis observes nothing. -/
def rectangle (axes : Fin d → String) (ports : Fin n → String) (port : Fin n)
    (window : Degrees d) : Manifest basis n d where
  axes := axes
  ports := ports
  slots := if ∀ i, 0 < window i then
    (grid d fun i => window i - 1).map fun degrees => ⟨port, degrees⟩ else []

end Manifest

/-- Why an observation could not be lowered. -/
inductive Failure where
  /-- The circuit contains series substitution, which has no lowering. -/
  | unsupported
  /-- The output manifest names a slot twice. -/
  | duplicateSlot
  /-- An axis or port ID is empty or repeated. -/
  | invalidNames
  /-- A term would exceed the size limit; lowering stopped there. -/
  | resourceLimit (limit : Nat)
  deriving Repr, DecidableEq

/-- Accept a term within the size limit. -/
def checked {n : Nat} (limit : Nat) (t : Term n d) : Except Failure (Term n d) :=
  if limit < t.size then .error (.resourceLimit limit) else .ok t

theorem checked_ok {n : Nat} {limit : Nat} {t r : Term n d} (ok : checked limit t = .ok r) :
    r = t := by
  unfold checked at ok
  split at ok <;> cases ok
  rfl

private theorem bind_ok {α β : Type} {x : Except Failure α} {f : α → Except Failure β} {r : β}
    (ok : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases ok
  | ok a => exact ⟨a, rfl, ok⟩

private theorem map_ok {α β : Type} {x : Except Failure α} {f : α → β} {r : β}
    (ok : x.map f = .ok r) : ∃ a, x = .ok a ∧ r = f a := by
  cases x with
  | error e => cases ok
  | ok a => cases ok; exact ⟨a, rfl, rfl⟩

/-- `Term.bind`, stopping as soon as a substituted term or a partial result
exceeds the limit. -/
def Term.bindChecked {n m : Nat} (limit : Nat) (substitute : Slot m d → Except Failure (Term n d)) :
    Term m d → Except Failure (Term n d)
  | .slot s => substitute s
  | .const q => .ok (.const q)
  | .add a b => do
      let a ← bindChecked limit substitute a
      let b ← bindChecked limit substitute b
      checked limit (.add a b)
  | .mul a b => do
      let a ← bindChecked limit substitute a
      let b ← bindChecked limit substitute b
      checked limit (.mul a b)

theorem Term.bindChecked_ok {n m : Nat} {limit : Nat}
    {substitute : Slot m d → Except Failure (Term n d)} {exact : Slot m d → Term n d}
    (agree : ∀ s r, substitute s = .ok r → r = exact s) :
    (t : Term m d) → (r : Term n d) → t.bindChecked limit substitute = .ok r →
      r = t.bind exact
  | .slot s, r, ok => agree s r ok
  | .const q, r, ok => by cases ok; rfl
  | .add a b, r, ok => by
      obtain ⟨a', ha, ok⟩ := bind_ok ok
      obtain ⟨b', hb, hr⟩ := bind_ok ok
      rw [checked_ok hr, bindChecked_ok agree a a' ha, bindChecked_ok agree b b' hb]
      rfl
  | .mul a b, r, ok => by
      obtain ⟨a', ha, ok⟩ := bind_ok ok
      obtain ⟨b', hb, hr⟩ := bind_ok ok
      rw [checked_ok hr, bindChecked_ok agree a a' ha, bindChecked_ok agree b b' hb]
      rfl

/-- How many splits a product at degree `k` sums over, without listing them. -/
def splits (k : Degrees d) : Nat := ∏ i, (k i + 1)

/-- A binary operation's term, refusing a product whose split count alone
exceeds the limit before listing the splits. -/
def lowerCheckedBinary (limit : Nat) (basis : Basis) (op : Binary d) (k : Degrees d) :
    Except Failure (Term 2 d) :=
  match op with
  | .product =>
      if limit < splits k then .error (.resourceLimit limit)
      else checked limit (lowerBinary basis .product k)
  | op => checked limit (lowerBinary basis op k)

/-- `lowerRaw`, stopping as soon as any term exceeds the limit, so expansion is
bounded rather than reported after the fact. `lowerChecked_ok` shows a result is
exactly `lowerRaw`'s. -/
def lowerChecked (limit : Nat) :
    {n m : Nat} → Circuit basis d n m → Fin m → Degrees d → Except Failure (Term n d)
  | _, _, .route f, j, k => checked limit (.slot ⟨f j, k⟩)
  | _, _, .constant q, _, k => checked limit (.const (constantCoefficient q k))
  | _, _, .axisVariable axis, _, k => checked limit (.const (variableCoefficient axis k))
  | _, _, .unary (.derivative axis), _, k =>
      checked limit (.mul (.const (derivativeFactor basis axis k))
        (.slot ⟨0, k.set axis (k axis + 1)⟩))
  | _, _, .binary op, _, k => lowerCheckedBinary limit basis op k
  | _, _, .compose a b, j, k => do
      let outer ← lowerChecked limit b j k
      outer.bindChecked limit fun s => lowerChecked limit a s.port s.degrees
  | _, _, .parallel (n := n) (k := p) a b, j, k =>
      Fin.addCases (motive := fun _ => Except Failure (Term (n + p) d))
        (fun j => (lowerChecked limit a j k).map (Term.mapPorts (Fin.castAdd p)))
        (fun j => (lowerChecked limit b j k).map (Term.mapPorts (Fin.natAdd n))) j

theorem lowerChecked_ok (limit : Nat) :
    {n m : Nat} → (c : Circuit basis d n m) → (j : Fin m) → (k : Degrees d) →
      (r : Term n d) → lowerChecked limit c j k = .ok r → r = lowerRaw c j k
  | _, _, .route _, _, _, _, ok | _, _, .constant _, _, _, _, ok
  | _, _, .axisVariable _, _, _, _, ok | _, _, .unary (.derivative _), _, _, _, ok =>
      checked_ok ok
  | _, _, .binary op, _, k, r, ok => by
      simp only [lowerChecked, lowerCheckedBinary] at ok
      cases op with
      | product =>
          simp only at ok
          split at ok
          · cases ok
          · exact checked_ok ok
      | add => exact checked_ok ok
      | integral _ => exact checked_ok ok
      | seriesCompose _ => exact checked_ok ok
  | _, _, .compose a b, j, k, r, ok => by
      obtain ⟨outer, houter, hr⟩ := bind_ok ok
      rw [Term.bindChecked_ok (fun s r ok => lowerChecked_ok limit a s.port s.degrees r ok)
        outer r hr, lowerChecked_ok limit b j k outer houter]
      rfl
  | _, _, .parallel (n := n) (k := p) a b, j, k, r, ok => by
      revert ok
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · intro ok
        simp only [lowerChecked, Fin.addCases_left] at ok
        obtain ⟨t, ht, rfl⟩ := map_ok ok
        simp only [lowerRaw, Fin.addCases_left, lowerChecked_ok limit a i k t ht]
      · intro ok
        simp only [lowerChecked, Fin.addCases_right] at ok
        obtain ⟨t, ht, rfl⟩ := map_ok ok
        simp only [lowerRaw, Fin.addCases_right, lowerChecked_ok limit b i k t ht]

/-- A polynomial expression over the dependency list, for the feedforward
circuit. Every slot of the term must be in the list. -/
def toExpr {n : Nat} (dependencies : List (Slot n d)) :
    Term n d → Gimle.Asgard.Polynomial.Expr dependencies.length
  | .slot s =>
      if bound : dependencies.idxOf s < dependencies.length then .var ⟨_, bound⟩
      else .constant 0
  | .const q => .constant q
  | .add a b => .add (toExpr dependencies a) (toExpr dependencies b)
  | .mul a b => .mul (toExpr dependencies a) (toExpr dependencies b)

/-- The dependency coefficients of a point, as the feedforward circuit's input. -/
noncomputable def dependencyPoint {n : Nat} (dependencies : List (Slot n d))
    (x : StreamPoint d n) : Point dependencies.length :=
  fun i => (x dependencies[i].port dependencies[i].degrees.toIndex : ℝ)

/-- The feedforward input is the manifest's extracted coefficients, cast. -/
theorem dependencyPoint_extract {n : Nat} (manifest : Manifest basis n d)
    (x : StreamPoint d n) (i : Fin manifest.slots.length) :
    dependencyPoint manifest.slots x i =
      ((manifest.extract x)[i]'(by simp [Manifest.extract]) : ℝ) := by
  simp [dependencyPoint, Manifest.extract]

theorem toExpr_eval {n : Nat} (dependencies : List (Slot n d)) (t : Term n d)
    (x : StreamPoint d n) (covered : ∀ s ∈ t.slots, s ∈ dependencies) :
    (toExpr dependencies t).eval (dependencyPoint dependencies x) = (t.eval x : ℝ) := by
  induction t with
  | slot s =>
      have member := covered s (by simp [Term.slots])
      have bound : dependencies.idxOf s < dependencies.length :=
        List.idxOf_lt_length_of_mem member
      simp only [toExpr, bound, dite_true, Gimle.Asgard.Polynomial.Expr.eval,
        dependencyPoint, Term.eval]
      have found : dependencies[dependencies.idxOf s]'bound = s := List.getElem_idxOf bound
      simp only [Fin.getElem_fin, found]
  | const q => rfl
  | add a b ha hb =>
      simp only [toExpr, Gimle.Asgard.Polynomial.Expr.eval, Term.eval, Rat.cast_add]
      rw [ha fun s h => covered s (by simp [Term.slots, h]),
        hb fun s h => covered s (by simp [Term.slots, h])]
  | mul a b ha hb =>
      simp only [toExpr, Gimle.Asgard.Polynomial.Expr.eval, Term.eval, Rat.cast_mul]
      rw [ha fun s h => covered s (by simp [Term.slots, h]),
        hb fun s h => covered s (by simp [Term.slots, h])]

/-- A lowered observation: the input coefficients it needs, and a feedforward
rational-polynomial circuit from them to the observed output coefficients. -/
structure Lowered (basis : Basis) (n m d : Nat) (output : Manifest basis m d) where
  inputs : Manifest basis n d
  circuit : Gimle.Asgard.Circuit inputs.slots.length output.slots.length

/-- The largest term size `lower` accepts by default. -/
def defaultLimit : Nat := 100000

/-- IDs must be non-empty and distinct. -/
def validNames {k : Nat} (names : Fin k → String) : Bool :=
  (List.ofFn names).Nodup && (List.ofFn names).all (· ≠ "")

/-- Lower an output observation of a stream circuit. The input manifest shares
the output's axes — a stream circuit has one ordered set of axes — and names the
circuit's input ports. -/
def lower {n m : Nat} (circuit : Circuit basis d n m) (inputPorts : Fin n → String)
    (output : Manifest basis m d) (limit : Nat := defaultLimit) :
    Except Failure (Lowered basis n m d output) :=
  if !supported circuit then .error .unsupported
  else if !(validNames output.axes && validNames output.ports && validNames inputPorts) then
    .error .invalidNames
  else if !output.slots.Nodup then .error .duplicateSlot
  else do
    -- Bounded first: fails as soon as any term would exceed the limit. Once it
    -- passes, `lowerRaw` gives the same terms (`lowerChecked_ok`).
    let _ ← output.slots.mapM fun s => lowerChecked limit circuit s.port s.degrees
    let terms := output.slots.map fun s => lowerRaw circuit s.port s.degrees
    let dependencies := (terms.flatMap Term.slots).dedup
    .ok ⟨⟨output.axes, inputPorts, dependencies⟩,
      Gimle.Asgard.Polynomial.compileOutputs fun o =>
        toExpr dependencies (lowerRaw circuit output.slots[o].port output.slots[o].degrees)⟩

/-- A successful lowering is of a supported circuit, which is defined on every
input, and its input manifest carries the output's axes and the given ports. -/
theorem lower_names {n m : Nat} (circuit : Circuit basis d n m)
    (inputPorts : Fin n → String) (output : Manifest basis m d) (limit : Nat)
    (lowered : Lowered basis n m d output)
    (ok : lower circuit inputPorts output limit = .ok lowered) :
    supported circuit = true ∧ lowered.inputs.axes = output.axes ∧
      lowered.inputs.ports = inputPorts := by
  unfold lower at ok
  by_cases support : supported circuit = true
  · simp only [support, Bool.not_true, Bool.false_eq_true, ite_false] at ok
    split at ok
    · cases ok
    · split at ok
      · cases ok
      · obtain ⟨_, _, ok⟩ := bind_ok ok
        cases ok
        exact ⟨support, rfl, rfl⟩
  · simp [support] at ok

/-- The observed circuit is defined on every input: no strict domain is skipped. -/
theorem lower_defined {n m : Nat} (circuit : Circuit basis d n m)
    (inputPorts : Fin n → String) (output : Manifest basis m d) (limit : Nat)
    (lowered : Lowered basis n m d output)
    (ok : lower circuit inputPorts output limit = .ok lowered) (x : StreamPoint d n) :
    circuit.Defined x :=
  supported_defined circuit (lower_names circuit inputPorts output limit lowered ok).1 x

/-- **A lowered observation is exact.** Running the lowered feedforward circuit
on the input coefficients its manifest names gives exactly the output
coefficients the output manifest names, of the original circuit, for every
input stream — whatever its coefficients outside those slots. -/
theorem lower_correct {n m : Nat} (circuit : Circuit basis d n m)
    (inputPorts : Fin n → String) (output : Manifest basis m d) (limit : Nat)
    (lowered : Lowered basis n m d output)
    (ok : lower circuit inputPorts output limit = .ok lowered) (x : StreamPoint d n) :
    lowered.circuit.run (dependencyPoint lowered.inputs.slots x) =
      fun o => (circuit.value x output.slots[o].port output.slots[o].degrees.toIndex : ℝ) := by
  have support := (lower_names circuit inputPorts output limit lowered ok).1
  unfold lower at ok
  simp only [support, Bool.not_true, Bool.false_eq_true, ite_false] at ok
  split at ok
  · cases ok
  · split at ok
    · cases ok
    · obtain ⟨_, _, ok⟩ := bind_ok ok
      cases ok
      funext o
      rw [Gimle.Asgard.Polynomial.compileOutputs_correct]
      simp only
      rw [lowerRaw_correct circuit support x]
      apply toExpr_eval
      intro s member
      rw [List.mem_dedup, List.mem_flatMap]
      exact ⟨_, List.mem_map.mpr ⟨output.slots[o], List.getElem_mem _, rfl⟩, member⟩

#print axioms sum_antidiagonal
#print axioms product_coefficient
#print axioms lowerRaw_correct
#print axioms lower_correct

end Gimle.Asgard.Streams.Lowering
