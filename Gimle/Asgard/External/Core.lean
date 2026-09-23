import Gimle.Asgard.Compile.Polynomial

/-! Pure pointwise external components. A symbol is a typed lookup key, not
proof of an implementation's identity. Every theorem retains the environment. -/
namespace Gimle.Asgard.External

def semanticVersion : String := "asgard.external-pointwise-real/v1"

structure Symbol (input output : Nat) where
  id : String
  version : String
  deriving Repr, DecidableEq, BEq

def Symbol.valid {n m : Nat} (s : Symbol n m) : Bool :=
  !s.id.isEmpty && !s.version.isEmpty

structure Component (n m : Nat) where
  domain : Point n → Prop
  value : Point n → Point m

abbrev Environment := {n m : Nat} → Symbol n m → Option (Component n m)

def resolve {n m : Nat} (env : Environment) (s : Symbol n m) : Option (Component n m) :=
  if s.valid then env s else none

def admitted {n m : Nat} (env : Environment) (s : Symbol n m) (x : Point n) : Prop :=
  match resolve env s with
  | none => False
  | some c => c.domain x

noncomputable def externalValue {n m : Nat} (env : Environment) (s : Symbol n m)
    (x : Point n) : Point m :=
  match resolve env s with
  | none => 0
  | some c => c.value x

inductive Circuit : Nat → Nat → Type where
  | embed {n m} (c : Gimle.Asgard.Circuit n m) : Circuit n m
  | external {n m} (s : Symbol n m) : Circuit n m
  | compose {n m k} (a : Circuit n m) (b : Circuit m k) : Circuit n k
  | parallel {n m k l} (a : Circuit n m) (b : Circuit k l) : Circuit (n+k) (m+l)

noncomputable def Circuit.value (env : Environment) {n m : Nat} : Circuit n m → Point n → Point m
  | .embed c, x => c.run x
  | .external s, x => externalValue env s x
  | .compose a b, x => b.value env (a.value env x)
  | .parallel a b, x => pointAppend (a.value env (pointLeft x)) (b.value env (pointRight x))

def Circuit.Defined (env : Environment) {n m : Nat} : Circuit n m → Point n → Prop
  | .embed _, _ => True
  | .external s, x => admitted env s x
  | .compose a b, x => a.Defined env x ∧ b.Defined env (a.value env x)
  | .parallel a b, x => a.Defined env (pointLeft x) ∧ b.Defined env (pointRight x)

def Circuit.Rel (env : Environment) {n m : Nat} : Circuit n m → Point n → Point m → Prop
  | .embed c, x, y => y = c.run x
  | .external s, x, y => admitted env s x ∧ y = externalValue env s x
  | .compose a b, x, y => ∃ z, a.Rel env x z ∧ b.Rel env z y
  | .parallel a b, x, y => ∃ u v,
      a.Rel env (pointLeft x) u ∧ b.Rel env (pointRight x) v ∧ y = pointAppend u v

theorem Circuit.rel_iff {n m : Nat} (c : Circuit n m) (env : Environment)
    (x : Point n) (y : Point m) : c.Rel env x y ↔ c.Defined env x ∧ y = c.value env x := by
  induction c with
  | embed c => simp [Rel, Defined, value]
  | external s => rfl
  | compose a b ha hb =>
    simp only [Rel, Defined, value, ha, hb]
    constructor
    · rintro ⟨z, ⟨hd, rfl⟩, hb⟩; exact ⟨⟨hd, hb.1⟩, hb.2⟩
    · rintro ⟨⟨ha, hb⟩, hy⟩; exact ⟨_, ⟨ha, rfl⟩, hb, hy⟩
  | parallel a b ha hb =>
    simp only [Rel, Defined, value, ha, hb]
    constructor
    · rintro ⟨u, v, ⟨hu, rfl⟩, ⟨hv, rfl⟩, hy⟩; exact ⟨⟨hu, hv⟩, hy⟩
    · rintro ⟨⟨hu, hv⟩, hy⟩; exact ⟨_, _, ⟨hu, rfl⟩, ⟨hv, rfl⟩, hy⟩

/-- Contract satisfaction promises actual definedness, not just a bound on any
outputs that happen to exist. Nonempty applicability is a separate assertion. -/
structure Contract (n m : Nat) where
  domain : Point n → Prop
  guarantee : Point n → Point m → Prop

def Circuit.Satisfies {n m : Nat} (c : Circuit n m) (env : Environment) (spec : Contract n m) : Prop :=
  ∀ x, spec.domain x → c.Defined env x ∧ spec.guarantee x (c.value env x)

def Contract.then {n m k : Nat} (a : Contract n m) (b : Contract m k) : Contract n k where
  domain := a.domain
  guarantee x y := ∃ z, a.guarantee x z ∧ b.guarantee z y

theorem Circuit.satisfies_compose {n m k : Nat} (a : Circuit n m) (b : Circuit m k)
    (env : Environment) (sa : Contract n m) (sb : Contract m k)
    (ha : a.Satisfies env sa) (hb : b.Satisfies env sb)
    (link : ∀ x z, sa.domain x → sa.guarantee x z → sb.domain z) :
    (a.compose b).Satisfies env (sa.then sb) := by
  intro x hx
  obtain ⟨had, hag⟩ := ha x hx
  obtain ⟨hbd, hbg⟩ := hb _ (link x _ hx hag)
  exact ⟨⟨had,hbd⟩, _,hag,hbg⟩

def Contract.parallel {n m k l : Nat} (a : Contract n m) (b : Contract k l) : Contract (n+k) (m+l) where
  domain x := a.domain (pointLeft x) ∧ b.domain (pointRight x)
  guarantee x y := a.guarantee (pointLeft x) (pointLeft y) ∧ b.guarantee (pointRight x) (pointRight y)

theorem Circuit.satisfies_parallel {n m k l : Nat} (a : Circuit n m) (b : Circuit k l)
    (env : Environment) (sa : Contract n m) (sb : Contract k l)
    (ha : a.Satisfies env sa) (hb : b.Satisfies env sb) :
    (a.parallel b).Satisfies env (sa.parallel sb) := by
  intro x hx
  obtain ⟨had,hag⟩ := ha _ hx.1
  obtain ⟨hbd,hbg⟩ := hb _ hx.2
  exact ⟨⟨had,hbd⟩, by simpa [Contract.parallel, value] using And.intro hag hbg⟩

def Circuit.Equivalent {n m : Nat} (env : Environment) (a b : Circuit n m) : Prop :=
  ∀ x y, a.Rel env x y ↔ b.Rel env x y

theorem Circuit.equivalent_of_domain_value {n m : Nat} (env : Environment) (a b : Circuit n m)
    (domains : ∀ x, a.Defined env x ↔ b.Defined env x)
    (values : ∀ x, a.Defined env x → a.value env x = b.value env x) : a.Equivalent env b := by
  intro x y
  rw [rel_iff, rel_iff]
  constructor
  · rintro ⟨hd,hy⟩; exact ⟨(domains x).mp hd, hy.trans (values x hd)⟩
  · rintro ⟨hd,hy⟩
    have ha := (domains x).mpr hd
    exact ⟨ha, hy.trans (values x ha).symm⟩

theorem Circuit.compose_congr {n m k : Nat} (env : Environment) (a b : Circuit n m)
    (c d : Circuit m k) (hab : a.Equivalent env b) (hcd : c.Equivalent env d) :
    (a.compose c).Equivalent env (b.compose d) := by
  intro x y
  change (∃ z, a.Rel env x z ∧ c.Rel env z y) ↔ ∃ z, b.Rel env x z ∧ d.Rel env z y
  constructor
  · rintro ⟨z, ha, hc⟩; exact ⟨z, (hab x z).mp ha, (hcd z y).mp hc⟩
  · rintro ⟨z, hb, hd⟩; exact ⟨z, (hab x z).mpr hb, (hcd z y).mpr hd⟩

#print axioms Circuit.rel_iff
#print axioms Circuit.satisfies_compose
#print axioms Circuit.satisfies_parallel
#print axioms Circuit.equivalent_of_domain_value
end Gimle.Asgard.External
