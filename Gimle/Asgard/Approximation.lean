import Gimle.Asgard.Rewrite

/-! Certified approximation for the existing total real circuit interpretation.
All quantitative facts reuse QuantitativeCircuitEquivalence. Numeric observations
are separate data and never construct these facts. -/
namespace Gimle.Asgard.Approximation

def schemaVersion : String := "asgard.circuit-approximation/v1"
def interpretationName : String := "asgard.feedforward.real.v1"
def metricName : String := "linf"

inductive Interpretation where | feedforwardReal deriving Repr, DecidableEq
inductive Metric where | linf deriving Repr, DecidableEq

structure Context where
  interpretation : Interpretation := .feedforwardReal
  metric : Metric := .linf
  deriving Repr, DecidableEq

def Context.parse (interpretation metric : String) : Except String Context :=
  if interpretation = interpretationName ∧ metric = metricName then .ok {}
  else .error "Unsupported approximation interpretation or metric"

/-- Nonnegativity is structural, including for empty regions and zero outputs. -/
structure Budget where
  value : ℚ
  nonnegative : 0 ≤ value

def Budget.ofRat (q : ℚ) : Option Budget :=
  if h : 0 ≤ q then some ⟨q,h⟩ else none

def Budget.add (a b : Budget) : Budget := ⟨a.value+b.value, add_nonneg a.nonnegative b.nonnegative⟩
def Budget.mul (a b : Budget) : Budget := ⟨a.value*b.value, mul_nonneg a.nonnegative b.nonnegative⟩

structure Claim (n m : Nat) where
  source : Circuit n m
  target : Circuit n m
  region : Point n → Prop
  error : Budget
  context : Context := {}

/-- Exactly the existing foundation linf relation, with rational allowance. -/
def Claim.Holds {n m : Nat} (claim : Claim n m) : Prop :=
  QuantitativeCircuitEquivalence claim.source claim.target claim.region claim.error.value

/-- Untrusted numerical data, indexed by the original typed circuit subjects.
No certified epsilon is inferred from measured error, loss or confidence. -/
structure Sample (n m : Nat) where
  input : Fin n → Float
  sourceOutput : Fin m → Float
  targetOutput : Fin m → Float

structure Observation {n m : Nat} (source target : Circuit n m) where
  datasetId : String
  regionDescription : String
  interpretation : String
  metric : String
  samples : Array (Sample n m)
  measuredMaximum : Float
  fittingLoss : Float
  statisticalConfidence : Option Float
  provenance : String

theorem close_symm {m : Nat} {a b : Point m} {e : ℝ} (h : LinfClose e a b) : LinfClose e b a := by
  intro i; simpa [abs_sub_comm] using h i

theorem close_trans {m : Nat} {a b c : Point m} {e d : ℝ}
    (hab : LinfClose e a b) (hbc : LinfClose d b c) : LinfClose (e+d) a c := by
  intro i
  exact (abs_sub_le (a i) (b i) (c i)).trans (add_le_add (hab i) (hbc i))

theorem symmetry {n m : Nat} {a b : Circuit n m} {region : Point n → Prop} {e : ℝ}
    (h : QuantitativeCircuitEquivalence a b region e) : QuantitativeCircuitEquivalence b a region e :=
  fun x hx => close_symm (h x hx)

theorem weaken {n m : Nat} {a b : Circuit n m} {region : Point n → Prop} {e d : ℝ}
    (h : QuantitativeCircuitEquivalence a b region e) (le : e ≤ d) :
    QuantitativeCircuitEquivalence a b region d := fun x hx i => (h x hx i).trans le

theorem transitivity {n m : Nat} {a b c : Circuit n m} {region : Point n → Prop} {e d : ℝ}
    (hab : QuantitativeCircuitEquivalence a b region e)
    (hbc : QuantitativeCircuitEquivalence b c region d) :
    QuantitativeCircuitEquivalence a c region (e+d) := fun x hx => close_trans (hab x hx) (hbc x hx)

theorem zero_iff_regional {n m : Nat} (a b : Circuit n m) (region : Point n → Prop) :
    QuantitativeCircuitEquivalence a b region 0 ↔ ∀ x, region x → a.run x = b.run x := by
  constructor
  · intro h x hx
    funext i
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (h x hx i) (abs_nonneg _)))
  · intro h x hx i; simp [h x hx]

theorem zero_global {n m : Nat} (a b : Circuit n m)
    (h : QuantitativeCircuitEquivalence a b (fun _ => True) 0) : GlobalCircuitEquivalence a b :=
  fun x => (zero_iff_regional a b _).mp h x trivial

theorem parallel {n m k l : Nat} {a b : Circuit n m} {c d : Circuit k l}
    {leftRegion : Point n → Prop} {rightRegion : Point k → Prop} {e f : ℝ}
    (left : QuantitativeCircuitEquivalence a b leftRegion e)
    (right : QuantitativeCircuitEquivalence c d rightRegion f) :
    QuantitativeCircuitEquivalence (a.parallel c) (b.parallel d)
      (fun x => leftRegion (pointLeft x) ∧ rightRegion (pointRight x)) (max e f) := by
  intro x hx i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simpa [Circuit.run, pointAppend] using (left _ hx.1 j).trans (le_max_left e f)
  · intro j
    simpa [Circuit.run, pointAppend] using (right _ hx.2 j).trans (le_max_right e f)

theorem precompose {n m k : Nat} (before : Circuit n m) {a b : Circuit m k}
    {inputRegion : Point n → Prop} {region : Point m → Prop} {e : ℝ}
    (h : QuantitativeCircuitEquivalence a b region e)
    (coverage : ∀ x, inputRegion x → region (before.run x)) :
    QuantitativeCircuitEquivalence (before.compose a) (before.compose b) inputRegion e :=
  fun x hx => h _ (coverage x hx)

/-- Pairwise linf sensitivity on a stated region. δ≥0 handles zero dimensions;
no differentiability, domain convexity or global extension is assumed. -/
def LipschitzOn {m k : Nat} (c : Circuit m k) (region : Point m → Prop) (gain : Budget) : Prop :=
  ∀ a b, region a → region b → ∀ delta : ℝ, 0 ≤ delta → LinfClose delta a b →
    LinfClose ((gain.value : ℝ)*delta) (c.run a) (c.run b)

theorem sequential {n m k : Nat} {a b : Circuit n m} {c d : Circuit m k}
    {inputRegion : Point n → Prop} {middleRegion : Point m → Prop} {e f : ℝ}
    (gain : Budget) (he : 0 ≤ e)
    (first : QuantitativeCircuitEquivalence a b inputRegion e)
    (second : QuantitativeCircuitEquivalence c d middleRegion f)
    (sensitivity : LipschitzOn c middleRegion gain)
    (coverage : ∀ x, inputRegion x → middleRegion (a.run x) ∧ middleRegion (b.run x)) :
    QuantitativeCircuitEquivalence (a.compose c) (b.compose d) inputRegion ((gain.value : ℝ)*e+f) := by
  intro x hx
  exact close_trans
    (sensitivity _ _ (coverage x hx).1 (coverage x hx).2 e he (first x hx))
    (second _ (coverage x hx).2)

def Claim.compose {n m k : Nat} (a : Claim n m) (b : Claim m k) (gain : Budget) : Claim n k where
  source := a.source.compose b.source
  target := a.target.compose b.target
  region := a.region
  error := (gain.mul a.error).add b.error

theorem Claim.compose_holds {n m k : Nat} (a : Claim n m) (b : Claim m k) (gain : Budget)
    (ha : a.Holds) (hb : b.Holds) (sensitivity : LipschitzOn b.source b.region gain)
    (coverage : ∀ x, a.region x → b.region (a.source.run x) ∧ b.region (a.target.run x)) :
    (a.compose b gain).Holds := by
  have he : (0 : ℝ) ≤ a.error.value := by exact_mod_cast a.error.nonnegative
  simpa [Holds, compose, Budget.add, Budget.mul] using sequential gain he ha hb sensitivity coverage

#print axioms zero_iff_regional
#print axioms parallel
#print axioms precompose
#print axioms sequential
#print axioms Claim.compose_holds
end Gimle.Asgard.Approximation
