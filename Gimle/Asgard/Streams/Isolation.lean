import Gimle.Asgard.Streams.Declaration
import Gimle.Asgard.Model.SourceSyntax

/-! # Isolating a scaled derivative in a stream equation

A **source equation** `lhs = rhs` is written in the source terms of
`Model.Term` (`term%`), such as `2 * diff(u, time) = diff(diff(u, space), space)`,
and names its unknown, the axis `along` it is isolated on and the boundary input
on that axis. Its meaning is the stream meaning of both sides: each is translated
to a `NamedExpr` (`NamedExpr.ofTerm`: a name is an input, `*` the stream product,
`-a` the product with `-1`, `diff(a, i)` the formal derivative along the axis
`i`), read through `Context.meaning`, and the two values are equal; the unknown
equals the boundary input on the whole zero slice along `along`, as in
`Equation.Solves`.

Isolation reads one side as `q * D_along(u) + r`, where `q` is an exact nonzero
literal product and `r` is free of every derivative of `u` along `along`, and
the other side `o` likewise. It returns the `Streams.Declaration` equation
`D_along u = (o - r) / q` with the same unknown, axis and boundary
(`SourceEquation.Isolated.equation`), with every term retained: nothing is
cancelled or dropped. Derivatives along other axes, such as the spatial
`D_x(D_x(u))` of heat, may appear anywhere in `o` and `r`.

`Isolated.solves_iff` relates the source relation to the isolated equation's
`Equation.Solves`, in both directions, so that `Equation.solves_iff_integral`
then gives its solution set: `u = integral((o - r)/q, b)` along `along`.

Rejected, each with a diagnostic that names an unsupported form, never an
unsatisfiable model: no derivative of `u` along `along` (`missingDerivative`),
one on both sides (`competingDerivative`), two on one side
(`repeatedDerivative`), a chain `D_t(D_t(u))` (`higherOrderDerivative`), a
mixed derivative such as `D_x(D_t(u))` or `D_t(D_x(u))` (`mixedDerivative`),
`D_t` of any other operand reading `u` (`unsupportedDerivative`), a non-literal
factor (`nonlinearDerivative`), a scale around a sum (`unsupportedDerivative`),
a zero scale (`zeroScale`), and integrals (`unsupportedIntegral`) and lambda
applications (`unsupportedApplication`), which have no stream reading here.
A name is always an input: axis variables are not written in this form. -/
namespace Gimle.Asgard.Streams

/-! ## Source terms as stream expressions -/

/-- The stream reading of a source term. -/
def NamedExpr.ofTerm : Model.Term → Except Model.ErrorCode NamedExpr
  | .var id => .ok (.input id)
  | .constant q => .ok (.constant q)
  | .add a b => do return .binary .add (← ofTerm a) (← ofTerm b)
  | .mul a b => do return .binary .product (← ofTerm a) (← ofTerm b)
  | .neg a => do return .binary .product (.constant (-1)) (← ofTerm a)
  | .derivative axis a => do return .unary (.derivative axis) (← ofTerm a)
  | .integral _ _ => .error .unsupportedIntegral
  | .apply _ _ _ => .error .unsupportedApplication

/-! ## Scaling -/

/-- Coefficientwise scaling by an exact rational. -/
def scaled {d : Nat} (q : ℚ) (a : Stream d) : Stream d := fun n => q * a n

theorem constant_apply {d : Nat} (basis : Basis) (q : ℚ) (n : Index d) :
    constant basis q n = if n = 0 then q else 0 := by
  cases basis with
  | ogf =>
    change MvPowerSeries.coeff n (MvPowerSeries.C q) = _
    rw [MvPowerSeries.coeff_C]
  | egf =>
    change factorial n * MvPowerSeries.coeff n (MvPowerSeries.C q) = _
    rw [MvPowerSeries.coeff_C]
    split
    · subst n; simp [factorial]
    · simp

/-- The product with a constant is coefficientwise scaling, in either basis. -/
theorem product_constant {d : Nat} (basis : Basis) (q : ℚ) (a : Stream d) :
    product basis (constant basis q) a = scaled q a := by
  funext n
  cases basis with
  | ogf =>
    change MvPowerSeries.coeff n (MvPowerSeries.C q * a) = _
    rw [MvPowerSeries.coeff_C_mul]
    rfl
  | egf =>
    change factorial n * MvPowerSeries.coeff n
      (decode .egf (encode .egf (MvPowerSeries.C q)) * decode .egf a) = _
    rw [decode_encode, MvPowerSeries.coeff_C_mul]
    change factorial n * (q * (a n / factorial n)) = q * a n
    field_simp [factorial_ne_zero n]

theorem product_comm {d : Nat} (basis : Basis) (a b : Stream d) :
    product basis a b = product basis b a := by
  rw [product, product, mul_comm]

theorem scaled_constant {d : Nat} (basis : Basis) (q c : ℚ) :
    scaled q (constant (d := d) basis c) = constant basis (q * c) := by
  funext n
  simp only [scaled, constant_apply]
  split <;> simp

theorem scaled_one {d : Nat} (a : Stream d) : scaled 1 a = a := by
  funext n; simp [scaled]

/-! ## Meaning relations -/

section Means
variable {d : Nat} {basis : Basis} {axes : String → Option (Fin d)}
  {inputs : String → Option (Stream d × Prop)}

/-- `e` resolves to the value `v` and its domain holds. -/
def NamedExpr.Means (basis : Basis) (axes : String → Option (Fin d))
    (inputs : String → Option (Stream d × Prop)) (e : NamedExpr) (v : Stream d) : Prop :=
  ∃ domain, e.meaning basis axes inputs = some (v, domain) ∧ domain

theorem NamedExpr.means_input (id : String) (v : Stream d) :
    (NamedExpr.input id).Means basis axes inputs v ↔
      ∃ domain, inputs id = some (v, domain) ∧ domain := Iff.rfl

theorem NamedExpr.means_constant (q : ℚ) (v : Stream d) :
    (NamedExpr.constant q).Means basis axes inputs v ↔ v = Gimle.Asgard.Streams.constant basis q := by
  simp only [Means, meaning, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨rfl, _⟩, _⟩; rfl
  · rintro rfl; exact ⟨True, ⟨rfl, rfl⟩, trivial⟩

theorem NamedExpr.means_derivative (axis : String) (a : NamedExpr) (v : Stream d) :
    (NamedExpr.unary (.derivative axis) a).Means basis axes inputs v ↔
      ∃ j va, axes axis = some j ∧ a.Means basis axes inputs va ∧ v = derivative basis j va := by
  simp only [Means, meaning, NamedUnary.resolve, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.map_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨_, ⟨j, hj, rfl⟩, ⟨va, da⟩, ha, rfl, rfl⟩, holds⟩
    exact ⟨j, va, hj, ⟨da, ha, holds⟩, rfl⟩
  · rintro ⟨j, va, hj, ⟨da, ha, holds⟩, rfl⟩
    exact ⟨da, ⟨_, ⟨j, hj, rfl⟩, (va, da), ha, rfl, rfl⟩, holds⟩

theorem NamedExpr.means_add (a b : NamedExpr) (v : Stream d) :
    (NamedExpr.binary .add a b).Means basis axes inputs v ↔
      ∃ va vb, a.Means basis axes inputs va ∧ b.Means basis axes inputs vb ∧ v = va + vb := by
  simp only [Means, meaning, NamedBinary.resolve, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨_, rfl, ⟨va, da⟩, ha, ⟨vb, db⟩, hb, rfl, rfl⟩, ⟨holdsA, holdsB⟩, _⟩
    exact ⟨va, vb, ⟨da, ha, holdsA⟩, ⟨db, hb, holdsB⟩, rfl⟩
  · rintro ⟨va, vb, ⟨da, ha, holdsA⟩, ⟨db, hb, holdsB⟩, rfl⟩
    exact ⟨_, ⟨_, rfl, (va, da), ha, (vb, db), hb, rfl, rfl⟩, ⟨holdsA, holdsB⟩, trivial⟩

theorem NamedExpr.means_product (a b : NamedExpr) (v : Stream d) :
    (NamedExpr.binary .product a b).Means basis axes inputs v ↔
      ∃ va vb, a.Means basis axes inputs va ∧ b.Means basis axes inputs vb ∧
        v = product basis va vb := by
  simp only [Means, meaning, NamedBinary.resolve, Option.pure_def, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨_, ⟨_, rfl, ⟨va, da⟩, ha, ⟨vb, db⟩, hb, rfl, rfl⟩, ⟨holdsA, holdsB⟩, _⟩
    exact ⟨va, vb, ⟨da, ha, holdsA⟩, ⟨db, hb, holdsB⟩, rfl⟩
  · rintro ⟨va, vb, ⟨da, ha, holdsA⟩, ⟨db, hb, holdsB⟩, rfl⟩
    exact ⟨_, ⟨_, rfl, (va, da), ha, (vb, db), hb, rfl, rfl⟩, ⟨holdsA, holdsB⟩, trivial⟩

/-- The product with a constant means coefficientwise scaling. -/
theorem NamedExpr.means_scaled (q : ℚ) (a : NamedExpr) (v : Stream d) :
    (NamedExpr.binary .product (.constant q) a).Means basis axes inputs v ↔
      ∃ va, a.Means basis axes inputs va ∧ v = scaled q va := by
  rw [means_product]
  simp only [means_constant]
  constructor
  · rintro ⟨_, va, rfl, ha, rfl⟩
    exact ⟨va, ha, product_constant basis q va⟩
  · rintro ⟨va, ha, rfl⟩
    exact ⟨_, va, rfl, ha, (product_constant basis q va).symm⟩

end Means

/-! ## Exact literal scales -/

/-- An exact literal product, such as `-1 * 2` (the reading of `-2`). -/
def NamedExpr.literal : NamedExpr → Option ℚ
  | .constant q => some q
  | .binary .product a b => do return (← a.literal) * (← b.literal)
  | _ => none

theorem NamedExpr.literal_means {d : Nat} {basis : Basis} {axes : String → Option (Fin d)}
    {inputs : String → Option (Stream d × Prop)} :
    ∀ (e : NamedExpr) (q : ℚ), e.literal = some q →
      ∀ v, (e.Means basis axes inputs v ↔ v = Gimle.Asgard.Streams.constant basis q)
  | .constant c, q, h, v => by
    simp only [literal, Option.some.injEq] at h
    subst h
    exact means_constant c v
  | .binary .product a b, q, h, v => by
    simp only [literal, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨qa, ha, qb, hb, rfl⟩ := h
    rw [means_product]
    simp only [literal_means a qa ha, literal_means b qb hb]
    constructor
    · rintro ⟨_, _, rfl, rfl, rfl⟩
      rw [product_constant, scaled_constant]
    · rintro rfl
      exact ⟨_, _, rfl, rfl, by rw [product_constant, scaled_constant]⟩
  | .input _, _, h, _ | .axisVariable _, _, h, _ | .unary _ _, _, h, _ => by simp [literal] at h
  | .binary .add _ _, _, h, _ | .binary (.integral _) _ _, _, h, _
  | .binary (.seriesCompose _) _ _, _, h, _ => by simp [literal] at h

/-! ## Affine recognition -/

/-- One side read as `scale * D_along(unknown) + remainder`; `none` means no
remainder was written. -/
structure Affine where
  scale : ℚ
  remainder : Option NamedExpr
  deriving Repr, DecidableEq

private def plusLeft (l : NamedExpr) : Option NamedExpr → NamedExpr
  | none => l
  | some r => .binary .add l r

private def plusRight (r : NamedExpr) : Option NamedExpr → NamedExpr
  | none => r
  | some l => .binary .add l r

/-- Of two findings of `NamedExpr.selfDerivative`, the first that names a form
other than a second bare `D_along(unknown)`; `fallback` when neither does. -/
private def specific (fallback : Model.ErrorCode) (a b : Option Model.ErrorCode) :
    Model.ErrorCode :=
  match a.filter (· != .competingDerivative), b.filter (· != .competingDerivative) with
  | some code, _ => code
  | none, some code => code
  | none, none => fallback

/-- Recognize a side containing exactly one derivative of `unknown` along
`along`, which must be the bare atom `D_along(unknown)`. Additive terms free of
such derivatives become the remainder, in source order; a scale is an exact
literal factor of a bare scaled atom. -/
def NamedExpr.affine (along unknown : String) : NamedExpr → Except Model.ErrorCode Affine
  | .unary (.derivative axis) a =>
    if axis = along ∧ a = .input unknown then .ok ⟨1, none⟩
    else .error (((NamedExpr.unary (.derivative axis) a).selfDerivative along unknown).getD
      .missingDerivative)
  | .binary .add a b =>
    if a.selfDerivative along unknown = none then do
      let p ← b.affine along unknown
      return ⟨p.scale, some (plusLeft a p.remainder)⟩
    else if b.selfDerivative along unknown = none then do
      let p ← a.affine along unknown
      return ⟨p.scale, some (plusRight b p.remainder)⟩
    else .error (specific .repeatedDerivative (a.selfDerivative along unknown)
      (b.selfDerivative along unknown))
  | .binary .product a b =>
    match a.literal, b.literal with
    | some c, _ => do
      let p ← b.affine along unknown
      if p.remainder.isSome then .error .unsupportedDerivative else return ⟨c * p.scale, none⟩
    | none, some c => do
      let p ← a.affine along unknown
      if p.remainder.isSome then .error .unsupportedDerivative else return ⟨p.scale * c, none⟩
    | none, none => .error .nonlinearDerivative
  | .binary (.integral _) _ _ | .binary (.seriesCompose _) _ _ => .error .unsupportedDerivative
  | .input _ | .constant _ | .axisVariable _ => .error .missingDerivative

section Affine
variable {d : Nat} {basis : Basis} {axes : String → Option (Fin d)}
  {inputs : String → Option (Stream d × Prop)}

/-- The meaning of an optional remainder; an absent one is `0`. -/
def RemainderMeans (basis : Basis) (axes : String → Option (Fin d))
    (inputs : String → Option (Stream d × Prop)) : Option NamedExpr → Stream d → Prop
  | none, r => r = 0
  | some e, r => e.Means basis axes inputs r

/-- The atom `D_along(unknown)`. -/
def atom (along unknown : String) : NamedExpr := .unary (.derivative along) (.input unknown)

private theorem means_plusLeft (l : NamedExpr) (rem : Option NamedExpr) (v : Stream d) :
    (plusLeft l rem).Means basis axes inputs v ↔
      ∃ vl r, l.Means basis axes inputs vl ∧ RemainderMeans basis axes inputs rem r ∧
        v = vl + r := by
  cases rem with
  | none =>
    simp only [plusLeft, RemainderMeans]
    constructor
    · intro h; exact ⟨v, 0, h, rfl, by simp⟩
    · rintro ⟨vl, r, h, rfl, rfl⟩; simpa using h
  | some r => exact NamedExpr.means_add l r v

private theorem means_plusRight (r : NamedExpr) (rem : Option NamedExpr) (v : Stream d) :
    (plusRight r rem).Means basis axes inputs v ↔
      ∃ vr l, r.Means basis axes inputs vr ∧ RemainderMeans basis axes inputs rem l ∧
        v = l + vr := by
  cases rem with
  | none =>
    simp only [plusRight, RemainderMeans]
    constructor
    · intro h; exact ⟨v, 0, h, rfl, by simp⟩
    · rintro ⟨vr, l, h, rfl, rfl⟩; simpa using h
  | some l =>
    rw [plusRight, NamedExpr.means_add]
    constructor
    · rintro ⟨vl, vr, hl, hr, rfl⟩; exact ⟨vr, vl, hr, hl, rfl⟩
    · rintro ⟨vr, vl, hr, hl, rfl⟩; exact ⟨vl, vr, hl, hr, rfl⟩

/-- **Affine recognition is exact.** A recognized side means
`scale * D_along(unknown) + remainder`, in every environment. -/
theorem NamedExpr.affine_means (along unknown : String) :
    ∀ (e : NamedExpr) (p : Affine), e.affine along unknown = .ok p → ∀ v,
      (e.Means basis axes inputs v ↔ ∃ a r, (atom along unknown).Means basis axes inputs a ∧
        RemainderMeans basis axes inputs p.remainder r ∧ v = scaled p.scale a + r)
  | .unary (.derivative axis) a, p, h, v => by
    unfold affine at h
    split at h
    · rename_i hatom
      obtain ⟨rfl, rfl⟩ := hatom
      simp only [Except.ok.injEq] at h
      subst h
      simp only [RemainderMeans, scaled_one]
      constructor
      · intro h; exact ⟨v, 0, h, rfl, by simp⟩
      · rintro ⟨a, _, h, rfl, rfl⟩; rw [add_zero]; exact h
    · cases h
  | .binary .add a b, p, h, v => by
    unfold affine at h
    split at h
    · cases hb : b.affine along unknown with
      | error _ => simp [hb, bind, Except.bind] at h
      | ok q =>
        simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        rw [means_add]
        simp only [affine_means along unknown b q hb, RemainderMeans, means_plusLeft]
        constructor
        · rintro ⟨va, vb, hva, ⟨at', r, hat, hr, rfl⟩, rfl⟩
          exact ⟨at', va + r, hat, ⟨va, r, hva, hr, rfl⟩, by abel⟩
        · rintro ⟨at', _, hat, ⟨va, r, hva, hr, rfl⟩, rfl⟩
          exact ⟨va, _, hva, ⟨at', r, hat, hr, rfl⟩, by abel⟩
    · split at h
      · cases ha : a.affine along unknown with
        | error _ => simp [ha, bind, Except.bind] at h
        | ok q =>
          simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          rw [means_add]
          simp only [affine_means along unknown a q ha, RemainderMeans, means_plusRight]
          constructor
          · rintro ⟨va, vb, ⟨at', l, hat, hl, rfl⟩, hvb, rfl⟩
            exact ⟨at', l + vb, hat, ⟨vb, l, hvb, hl, rfl⟩, by abel⟩
          · rintro ⟨at', _, hat, ⟨vb, l, hvb, hl, rfl⟩, rfl⟩
            exact ⟨_, vb, ⟨at', l, hat, hl, rfl⟩, hvb, by abel⟩
      · cases h
  | .binary .product a b, p, h, v => by
    unfold affine at h
    split at h
    · rename_i c hc
      cases hb : b.affine along unknown with
      | error _ => simp [hb, bind, Except.bind] at h
      | ok q =>
        cases hq : q.remainder with
        | some _ => simp [hb, hq, bind, Except.bind] at h
        | none =>
          simp only [hb, hq, bind, Except.bind, Option.isSome_none, Bool.false_eq_true,
            if_false, pure, Except.pure, Except.ok.injEq] at h
          subst h
          have hbm := affine_means along unknown b q hb
          rw [hq] at hbm
          rw [means_product]
          simp only [literal_means a c hc, hbm, RemainderMeans]
          constructor
          · rintro ⟨_, _, rfl, ⟨at', _, hat, rfl, rfl⟩, rfl⟩
            refine ⟨at', 0, hat, rfl, ?_⟩
            funext n
            simp only [product_constant, scaled, add_zero]
            ring
          · rintro ⟨at', _, hat, rfl, rfl⟩
            refine ⟨_, _, rfl, ⟨at', 0, hat, rfl, rfl⟩, ?_⟩
            funext n
            simp only [product_constant, scaled, add_zero]
            ring
    · rename_i c _ hc
      cases ha : a.affine along unknown with
      | error _ => simp [ha, bind, Except.bind] at h
      | ok q =>
        cases hq : q.remainder with
        | some _ => simp [ha, hq, bind, Except.bind] at h
        | none =>
          simp only [ha, hq, bind, Except.bind, Option.isSome_none, Bool.false_eq_true,
            if_false, pure, Except.pure, Except.ok.injEq] at h
          subst h
          have ham := affine_means along unknown a q ha
          rw [hq] at ham
          rw [means_product]
          simp only [literal_means b c hc, ham, RemainderMeans]
          constructor
          · rintro ⟨_, _, ⟨at', _, hat, rfl, rfl⟩, rfl, rfl⟩
            refine ⟨at', 0, hat, rfl, ?_⟩
            funext n
            simp only [product_comm _ _ (Gimle.Asgard.Streams.constant _ _), product_constant,
              scaled, add_zero]
            ring
          · rintro ⟨at', _, hat, rfl, rfl⟩
            refine ⟨_, _, ⟨at', 0, hat, rfl, rfl⟩, rfl, ?_⟩
            funext n
            simp only [product_comm _ _ (Gimle.Asgard.Streams.constant _ _), product_constant,
              scaled, add_zero]
            ring
    · cases h
  | .binary (.integral _) _ _, _, h, _ | .binary (.seriesCompose _) _ _, _, h, _
  | .input _, _, h, _ | .constant _, _, h, _ | .axisVariable _, _, h, _ => by
    simp [affine] at h

/-- A recognized remainder is free of every derivative of `unknown` along `along`. -/
theorem NamedExpr.affine_free (along unknown : String) :
    ∀ (e : NamedExpr) (p : Affine), e.affine along unknown = .ok p →
      ∀ r, p.remainder = some r → r.selfDerivative along unknown = none
  | .unary (.derivative axis) a, p, h, r, hr => by
    unfold affine at h
    split at h
    · simp only [Except.ok.injEq] at h
      subst h
      cases hr
    · cases h
  | .binary .add a b, p, h, r, hr => by
    unfold affine at h
    split at h
    · rename_i free
      cases hb : b.affine along unknown with
      | error _ => simp [hb, bind, Except.bind] at h
      | ok q =>
        simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        simp only [Option.some.injEq] at hr
        subst hr
        cases hq : q.remainder with
        | none => simpa [plusLeft] using free
        | some r' =>
          simp [plusLeft, selfDerivative, free, affine_free along unknown b q hb r' hq]
    · split at h
      · rename_i free
        cases ha : a.affine along unknown with
        | error _ => simp [ha, bind, Except.bind] at h
        | ok q =>
          simp only [ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
          subst h
          simp only [Option.some.injEq] at hr
          subst hr
          cases hq : q.remainder with
          | none => simpa [plusRight] using free
          | some r' =>
            simp [plusRight, selfDerivative, free, affine_free along unknown a q ha r' hq]
      · cases h
  | .binary .product a b, p, h, r, hr => by
    unfold affine at h
    split at h
    · cases hb : b.affine along unknown with
      | error _ => simp [hb, bind, Except.bind] at h
      | ok q =>
        cases hq : q.remainder <;>
          simp [hb, hq, bind, Except.bind, pure, Except.pure] at h
        subst h
        cases hr
    · cases ha : a.affine along unknown with
      | error _ => simp [ha, bind, Except.bind] at h
      | ok q =>
        cases hq : q.remainder <;>
          simp [ha, hq, bind, Except.bind, pure, Except.pure] at h
        subst h
        cases hr
    · cases h
  | .binary (.integral _) _ _, _, h, _, _ | .binary (.seriesCompose _) _ _, _, h, _, _
  | .input _, _, h, _, _ | .constant _, _, h, _, _ | .axisVariable _, _, h, _, _ => by
    simp [affine] at h

end Affine

/-! ## The isolated right-hand side -/

/-- `opposite - remainder`, the subtraction written as the product with `-1`;
`opposite` when no remainder was written. -/
def difference (opposite : NamedExpr) : Option NamedExpr → NamedExpr
  | none => opposite
  | some r => .binary .add opposite (.binary .product (.constant (-1)) r)

/-- `(opposite - remainder) / scale`, written without a unit factor. -/
def isolatedRhs (scale : ℚ) (opposite : NamedExpr) (remainder : Option NamedExpr) :
    NamedExpr :=
  if scale = 1 then difference opposite remainder
  else .binary .product (.constant scale⁻¹) (difference opposite remainder)

section Rhs
variable {d : Nat} {basis : Basis} {axes : String → Option (Fin d)}
  {inputs : String → Option (Stream d × Prop)}

theorem difference_means (o : NamedExpr) (rem : Option NamedExpr) (w : Stream d) :
    (difference o rem).Means basis axes inputs w ↔ ∃ vo r, o.Means basis axes inputs vo ∧
      RemainderMeans basis axes inputs rem r ∧ w = vo + scaled (-1) r := by
  cases rem with
  | none =>
    simp only [difference, RemainderMeans]
    constructor
    · intro h
      refine ⟨w, 0, h, rfl, ?_⟩
      funext n
      change w n = w n + -1 * 0
      ring
    · rintro ⟨vo, _, h, rfl, rfl⟩
      have : vo + scaled (-1) (0 : Stream d) = vo := by
        funext n
        change vo n + -1 * 0 = vo n
        ring
      rw [this]; exact h
  | some r =>
    simp only [difference, RemainderMeans, NamedExpr.means_add, NamedExpr.means_scaled]
    constructor
    · rintro ⟨vo, _, ho, ⟨vr, hr, rfl⟩, rfl⟩; exact ⟨vo, vr, ho, hr, rfl⟩
    · rintro ⟨vo, vr, ho, hr, rfl⟩; exact ⟨vo, _, ho, ⟨vr, hr, rfl⟩, rfl⟩

theorem isolatedRhs_means (q : ℚ) (o : NamedExpr) (rem : Option NamedExpr) (w : Stream d) :
    (isolatedRhs q o rem).Means basis axes inputs w ↔ ∃ vo r,
      o.Means basis axes inputs vo ∧ RemainderMeans basis axes inputs rem r ∧
        w = scaled q⁻¹ (vo + scaled (-1) r) := by
  unfold isolatedRhs
  split
  · rename_i one
    subst one
    rw [difference_means]
    simp only [inv_one, scaled_one]
  · rw [NamedExpr.means_scaled]
    simp only [difference_means]
    constructor
    · rintro ⟨_, ⟨vo, r, ho, hr, rfl⟩, rfl⟩; exact ⟨vo, r, ho, hr, rfl⟩
    · rintro ⟨vo, r, ho, hr, rfl⟩; exact ⟨_, ⟨vo, r, ho, hr, rfl⟩, rfl⟩

end Rhs

theorem isolatedRhs_free (along unknown : String) (q : ℚ) (o : NamedExpr)
    (rem : Option NamedExpr) (free : o.selfDerivative along unknown = none)
    (remFree : ∀ r, rem = some r → r.selfDerivative along unknown = none) :
    (isolatedRhs q o rem).selfDerivative along unknown = none := by
  have diff : (difference o rem).selfDerivative along unknown = none := by
    cases rem with
    | none => exact free
    | some r => simp [difference, NamedExpr.selfDerivative, free, remFree r rfl]
  unfold isolatedRhs
  split
  · exact diff
  · simp [NamedExpr.selfDerivative, diff]

/-! ## Source equations -/

/-- `lhs = rhs` in source terms, isolated for `unknown` along the axis `along`,
with `unknown` equal to the input `boundary` on the whole zero slice along that
axis. All three are stable IDs. -/
structure SourceEquation where
  unknown : String
  along : String
  boundary : String
  lhs : Model.Term
  rhs : Model.Term
  deriving Repr, DecidableEq

/-- The side holding the derivative of `unknown` along `along` first. The other
side must hold none; when both do, a mixed or higher-order form on either side
is reported before `competingDerivative`. -/
def orient (along unknown : String) (lhs rhs : NamedExpr) :
    Except Model.ErrorCode {sides : NamedExpr × NamedExpr //
      ((sides.1 = lhs ∧ sides.2 = rhs) ∨ (sides.1 = rhs ∧ sides.2 = lhs)) ∧
        sides.2.selfDerivative along unknown = none} :=
  match hl : lhs.selfDerivative along unknown, hr : rhs.selfDerivative along unknown with
  | none, none => .error .missingDerivative
  | some _, none => .ok ⟨(lhs, rhs), .inl ⟨rfl, rfl⟩, hr⟩
  | none, some _ => .ok ⟨(rhs, lhs), .inr ⟨rfl, rfl⟩, hl⟩
  | some a, some b => .error (specific .competingDerivative (some a) (some b))

/-- A successful isolation keeps the translated sides it read and the facts it
checked. -/
structure SourceEquation.Isolated (se : SourceEquation) where
  lhs : NamedExpr
  rhs : NamedExpr
  translatedLhs : NamedExpr.ofTerm se.lhs = .ok lhs
  translatedRhs : NamedExpr.ofTerm se.rhs = .ok rhs
  side : NamedExpr
  opposite : NamedExpr
  sides : (side = lhs ∧ opposite = rhs) ∨ (side = rhs ∧ opposite = lhs)
  explicit : opposite.selfDerivative se.along se.unknown = none
  affine : Affine
  recognized : side.affine se.along se.unknown = .ok affine
  nonzero : affine.scale ≠ 0

/-- The isolated equation `D_along unknown = (opposite - remainder) / scale`,
with the source's unknown, axis and boundary. -/
def SourceEquation.Isolated.equation {se : SourceEquation} (i : se.Isolated) : Equation :=
  ⟨se.unknown, se.along, se.boundary, isolatedRhs i.affine.scale i.opposite i.affine.remainder⟩

/-- Translate both sides, orient them and recognize the affine side. A
diagnostic names the unknown and the side (`lhs`, `rhs`) that failed to
translate, or the axis it failed to isolate on. -/
def SourceEquation.isolate (se : SourceEquation) : Except Model.Diagnostic se.Isolated :=
  match hl : NamedExpr.ofTerm se.lhs, hr : NamedExpr.ofTerm se.rhs with
  | .error code, _ => .error ⟨code, se.unknown, "lhs"⟩
  | .ok _, .error code => .error ⟨code, se.unknown, "rhs"⟩
  | .ok lhs, .ok rhs =>
    match orient se.along se.unknown lhs rhs with
    | .error code => .error ⟨code, se.unknown, se.along⟩
    | .ok ⟨(side, opposite), sides, explicit⟩ =>
      match hp : side.affine se.along se.unknown with
      | .error code => .error ⟨code, se.unknown, se.along⟩
      | .ok p =>
        if hs : p.scale = 0 then .error ⟨.zeroScale, se.unknown, se.along⟩
        else .ok ⟨lhs, rhs, hl, hr, side, opposite, sides, explicit, p, hp, hs⟩

/-- **The initial profile is kept.** The isolated equation has the source's
unknown, axis and boundary input. -/
theorem SourceEquation.Isolated.keeps {se : SourceEquation} (i : se.Isolated) :
    i.equation.unknown = se.unknown ∧ i.equation.along = se.along ∧
      i.equation.boundary = se.boundary := ⟨rfl, rfl, rfl⟩

/-- **The isolated right-hand side is explicit**: it has no derivative of the
unknown along its own axis, so `Declaration.validate` does not refuse it for one. -/
theorem SourceEquation.Isolated.explicit_rhs {se : SourceEquation} (i : se.Isolated) :
    i.equation.rhs.selfDerivative se.along se.unknown = none :=
  isolatedRhs_free _ _ _ _ _ i.explicit
    (NamedExpr.affine_free _ _ i.side i.affine i.recognized)

/-- The source relation: both sides translate, their stream meanings (through
`Context.meaning`) are defined and equal, and the unknown equals the boundary
input on the whole zero slice along the declared axis. -/
def SourceEquation.Solves (se : SourceEquation) (c : Context) (basis : Basis)
    (x : StreamPoint c.axes.length c.inputs.length) : Prop :=
  ∃ lhs rhs, NamedExpr.ofTerm se.lhs = .ok lhs ∧ NamedExpr.ofTerm se.rhs = .ok rhs ∧
    ∃ unknown along boundary value lhsDomain rhsDomain,
      c.input se.unknown = some unknown ∧ c.axis se.along = some along ∧
      c.input se.boundary = some boundary ∧
      c.meaning basis lhs x = some (value, lhsDomain) ∧ lhsDomain ∧
      c.meaning basis rhs x = some (value, rhsDomain) ∧ rhsDomain ∧
      ∀ k : Index c.axes.length, k along = 0 → x unknown k = x boundary k

private theorem solve_scaled {d : Nat} (q : ℚ) (nonzero : q ≠ 0) (a r v : Stream d) :
    v = scaled q a + r ↔ a = scaled q⁻¹ (v + scaled (-1) r) := by
  constructor
  · rintro rfl
    funext n
    change a n = q⁻¹ * ((q * a n + r n) + -1 * r n)
    field_simp
    ring
  · rintro rfl
    funext n
    change v n = q * (q⁻¹ * (v n + -1 * r n)) + r n
    field_simp
    ring

/-- **Isolation preserves the stream equation**, in both directions: a point
solves the source equation exactly when it solves the isolated
`D_along u = (o - r) / q`, with the same boundary. -/
theorem SourceEquation.Isolated.solves_iff {se : SourceEquation} (i : se.Isolated) (c : Context)
    (basis : Basis) (x : StreamPoint c.axes.length c.inputs.length) :
    se.Solves c basis x ↔ i.equation.Solves c basis x := by
  by_cases valid : c.valid
  swap
  · have none : c.input se.unknown = none := by simp [Context.input, valid]
    simp [SourceEquation.Solves, Equation.Solves, Isolated.equation, none]
  let inputs : String → Option (Stream c.axes.length × Prop) :=
    fun id => (c.input id).map fun j => (x j, True)
  have means : ∀ e v, (∃ domain, c.meaning basis e x = some (v, domain) ∧ domain) ↔
      e.Means basis c.axis inputs v := by
    intro e v
    simp only [Context.meaning, valid, if_true, NamedExpr.Means, inputs]
  -- The atom `D_along(unknown)` means the derivative of the unknown's stream.
  have atom_means : ∀ u j a, c.input se.unknown = some u → c.axis se.along = some j →
      ((atom se.along se.unknown).Means basis c.axis inputs a ↔ a = derivative basis j (x u)) := by
    intro u j a hu hj
    simp only [atom, NamedExpr.means_derivative, NamedExpr.means_input, inputs, hu, hj,
      Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨_, _, rfl, ⟨_, ⟨rfl, rfl⟩, _⟩, rfl⟩; rfl
    · rintro rfl; exact ⟨j, x u, rfl, ⟨True, ⟨rfl, rfl⟩, trivial⟩, rfl⟩
  have core : ∀ u j, c.input se.unknown = some u → c.axis se.along = some j →
      ((∃ v, i.side.Means basis c.axis inputs v ∧ i.opposite.Means basis c.axis inputs v) ↔
        i.equation.rhs.Means basis c.axis inputs (derivative basis j (x u))) := by
    intro u j hu hj
    simp only [Isolated.equation, isolatedRhs_means,
      NamedExpr.affine_means se.along se.unknown i.side i.affine i.recognized,
      atom_means u j _ hu hj]
    constructor
    · rintro ⟨v, ⟨_, r, rfl, hr, hv⟩, ho⟩
      exact ⟨v, r, ho, hr, (solve_scaled _ i.nonzero _ _ _).mp hv⟩
    · rintro ⟨vo, r, ho, hr, hv⟩
      exact ⟨vo, ⟨_, r, rfl, hr, (solve_scaled _ i.nonzero _ _ _).mpr hv⟩, ho⟩
  have sides : (∃ v, i.lhs.Means basis c.axis inputs v ∧ i.rhs.Means basis c.axis inputs v) ↔
      ∃ v, i.side.Means basis c.axis inputs v ∧ i.opposite.Means basis c.axis inputs v := by
    rcases i.sides with ⟨hs, ho⟩ | ⟨hs, ho⟩
    · rw [hs, ho]
    · rw [hs, ho]
      constructor <;> rintro ⟨v, h1, h2⟩ <;> exact ⟨v, h2, h1⟩
  constructor
  · rintro ⟨lhs, rhs, hl, hr, u, j, b, v, dl, dr, hu, hj, hb, ml, holdsL, mr, holdsR, slice⟩
    rw [i.translatedLhs, Except.ok.injEq] at hl
    rw [i.translatedRhs, Except.ok.injEq] at hr
    subst hl hr
    have found := sides.mp ⟨v, (means _ _).mp ⟨dl, ml, holdsL⟩, (means _ _).mp ⟨dr, mr, holdsR⟩⟩
    obtain ⟨domain, hm, holds⟩ := (means _ _).mpr ((core u j hu hj).mp found)
    exact ⟨u, j, b, _, domain, hu, hj, hb, hm, holds, rfl, slice⟩
  · rintro ⟨u, j, b, value, domain, hu, hj, hb, hm, holds, slope, slice⟩
    subst slope
    obtain ⟨v, hl, hr⟩ := sides.mpr ((core u j hu hj).mpr ((means _ _).mp ⟨domain, hm, holds⟩))
    obtain ⟨dl, ml, holdsL⟩ := (means _ _).mpr hl
    obtain ⟨dr, mr, holdsR⟩ := (means _ _).mpr hr
    exact ⟨i.lhs, i.rhs, i.translatedLhs, i.translatedRhs, u, j, b, v, dl, dr, hu, hj, hb, ml,
      holdsL, mr, holdsR, slice⟩

/-! ## Source declarations -/

/-- A stream declaration whose equations are source equations: basis, ordered
axes and inputs as in `Declaration`. -/
structure SourceDeclaration where
  basis : Basis
  axes : List Axis
  inputs : List Polynomial.Port
  equations : List SourceEquation
  deriving Repr, DecidableEq

/-- The named context both sides resolve in, in declared order. -/
def SourceDeclaration.context (s : SourceDeclaration) : Context := ⟨s.axes, s.inputs⟩

/-- The stream declaration with the same basis, axes and inputs and the given
equations. Its context is `s.context`. -/
def SourceDeclaration.isolated (s : SourceDeclaration) (equations : List Equation) :
    Declaration := ⟨s.basis, s.axes, s.inputs, equations⟩

/-- Isolate every equation, in declared order; the first failure is reported. -/
def SourceDeclaration.isolate (s : SourceDeclaration) : Except Model.Diagnostic (List Equation) :=
  s.equations.mapM fun se => SourceEquation.Isolated.equation <$> se.isolate

/-- Isolate, then validate and resolve the isolated declaration
(`Declaration.compile`). -/
def SourceDeclaration.compile (s : SourceDeclaration) :
    Except Model.Diagnostic ((equations : List Equation) × StreamModel (s.isolated equations)) := do
  let equations ← s.isolate
  let model ← (s.isolated equations).compile
  return ⟨equations, model⟩

/-- Every source equation holds. -/
def SourceDeclaration.Solves (s : SourceDeclaration)
    (x : StreamPoint s.context.axes.length s.context.inputs.length) : Prop :=
  ∀ se ∈ s.equations, se.Solves s.context s.basis x

private theorem forall₂_of_mapM {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = .ok l' →
      List.Forall₂ (fun a b => f a = .ok b) l l'
  | [], l', h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .nil
  | a :: l, l', h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | error _ => simp [ha, bind, Except.bind] at h
    | ok b =>
      cases hl : l.mapM f with
      | error _ => simp [ha, hl, bind, Except.bind] at h
      | ok bs =>
        simp only [ha, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
        subst h
        exact .cons ha (forall₂_of_mapM hl)

private theorem forall_iff_of_forall₂ {α β : Type} {R : α → β → Prop} {P : α → Prop}
    {Q : β → Prop} (link : ∀ a b, R a b → (P a ↔ Q b)) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ((∀ a ∈ l, P a) ↔ ∀ b ∈ l', Q b)
  | _, _, .nil => by simp
  | _, _, .cons h rest => by
    simp only [List.forall_mem_cons]
    rw [link _ _ h, forall_iff_of_forall₂ link rest]

/-- **The declaration's solution set is kept.** A point solves the source
declaration exactly when it solves the isolated one. -/
theorem SourceDeclaration.solves_iff (s : SourceDeclaration) (equations : List Equation)
    (isolated : s.isolate = .ok equations)
    (x : StreamPoint s.context.axes.length s.context.inputs.length) :
    s.Solves x ↔ (s.isolated equations).Solves x := by
  refine forall_iff_of_forall₂ (fun se eq found => ?_) (forall₂_of_mapM isolated)
  cases hi : se.isolate with
  | error _ => simp [hi, Functor.map, Except.map] at found
  | ok i =>
    simp only [hi, Functor.map, Except.map, Except.ok.injEq] at found
    subst found
    exact i.solves_iff s.context s.basis x

/-! ## Source notation -/

/-- `sourceEquation% (u, t, b) lhs = rhs` is the source equation `lhs = rhs` for
the unknown `u` along the axis `t` with boundary input `b`, both sides in the
`term%` notation of `Model.SourceSyntax`, such as
`sourceEquation% (u, time, boundary) 2 * diff(u, time) = diff(diff(u, space), space)`. -/
syntax "sourceEquation%" "(" ident "," ident "," ident ")" asgardTerm " = " asgardTerm : term
macro_rules
  | `(sourceEquation% ($u:ident, $along:ident, $boundary:ident) $lhs:asgardTerm = $rhs:asgardTerm) =>
    `(SourceEquation.mk $(Lean.quote u.getId.toString) $(Lean.quote along.getId.toString)
      $(Lean.quote boundary.getId.toString) (term% $lhs) (term% $rhs))

#print axioms product_constant
#print axioms NamedExpr.literal_means
#print axioms NamedExpr.affine_means
#print axioms NamedExpr.affine_free
#print axioms isolatedRhs_means
#print axioms SourceEquation.Isolated.explicit_rhs
#print axioms SourceEquation.Isolated.solves_iff
#print axioms SourceDeclaration.solves_iff
end Gimle.Asgard.Streams
