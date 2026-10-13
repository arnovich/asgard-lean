import Gimle.Asgard.Streams.Core

/-! Independent coefficient expressions compile through typed stream wiring.
Substitution domains remain strict even when a later operation discards data. -/
namespace Gimle.Asgard.Streams

inductive Unary (d : Nat) where
  | derivative (axis : Fin d)
  deriving Repr, DecidableEq

inductive Binary (d : Nat) where
  | add | product
  | integral (axis : Fin d)
  | seriesCompose (axis : Fin d)
  deriving Repr, DecidableEq

/-- Historical theory spelling: convolution means selected-variable formal
substitution, with the identical zero-constant admission condition. It does not
name a discrete spatial kernel or coefficientwise fiber product. -/
def Binary.convolution {d : Nat} (axis : Fin d) : Binary d := .seriesCompose axis

noncomputable def Unary.value {d : Nat} (basis : Basis) : Unary d → Stream d → Stream d
  | .derivative i, a => Gimle.Asgard.Streams.derivative basis i a

noncomputable def Binary.value {d : Nat} (basis : Basis) :
    Binary d → Stream d → Stream d → Stream d
  | .add, a, b => a + b
  | .product, a, b => Gimle.Asgard.Streams.product basis a b
  | .integral i, a, b => Gimle.Asgard.Streams.integral basis i a b
  | .seriesCompose i, a, b => Gimle.Asgard.Streams.seriesCompose basis i a b

def Binary.Domain {d : Nat} (basis : Basis) : Binary d → Stream d → Stream d → Prop
  | .seriesCompose _, _, b => CanCompose basis b
  | _, _, _ => True

def append {d n m : Nat} (a : StreamPoint d n) (b : StreamPoint d m) : StreamPoint d (n+m) :=
  Fin.addCases a b

def left {d n m : Nat} (x : StreamPoint d (n+m)) : StreamPoint d n := fun i => x (i.castAdd m)
def right {d n m : Nat} (x : StreamPoint d (n+m)) : StreamPoint d m := fun i => x (i.natAdd n)

@[simp] theorem left_append {d n m : Nat} (a : StreamPoint d n) (b : StreamPoint d m) :
    left (append a b) = a := by
  funext i
  change Fin.addCases a b (i.castAdd m) = a i
  rw [Fin.addCases_left]

@[simp] theorem right_append {d n m : Nat} (a : StreamPoint d n) (b : StreamPoint d m) :
    right (append a b) = b := by
  funext i
  change Fin.addCases a b (i.natAdd n) = b i
  rw [Fin.addCases_right]

@[simp] theorem append_single {d : Nat} (a b : Stream d) : append ![a] ![b] = ![a,b] := by
  funext i
  fin_cases i <;> rfl

inductive Circuit (basis : Basis) (d : Nat) : Nat → Nat → Type where
  | route {n m} (indices : Fin m → Fin n) : Circuit basis d n m
  | constant (q : ℚ) : Circuit basis d 0 1
  | axisVariable (axis : Fin d) : Circuit basis d 0 1
  | unary (op : Unary d) : Circuit basis d 1 1
  | binary (op : Binary d) : Circuit basis d 2 1
  | compose {n m o} (first : Circuit basis d n m) (second : Circuit basis d m o) : Circuit basis d n o
  | parallel {n m k o} (a : Circuit basis d n m) (b : Circuit basis d k o) : Circuit basis d (n+k) (m+o)

noncomputable def Circuit.value {basis : Basis} {d n m : Nat} :
    Circuit basis d n m → StreamPoint d n → StreamPoint d m
  | .route f, x => x ∘ f
  | .constant q, _ => ![Gimle.Asgard.Streams.constant basis q]
  | .axisVariable i, _ => ![Gimle.Asgard.Streams.axisVariable basis i]
  | .unary op, x => ![op.value basis (x 0)]
  | .binary op, x => ![op.value basis (x 0) (x 1)]
  | .compose a b, x => b.value (a.value x)
  | .parallel a b, x => append (a.value (left x)) (b.value (right x))

def Circuit.Defined {basis : Basis} {d n m : Nat} : Circuit basis d n m → StreamPoint d n → Prop
  | .route _, _ | .constant _, _ | .axisVariable _, _ | .unary _, _ => True
  | .binary op, x => op.Domain basis (x 0) (x 1)
  | .compose a b, x => a.Defined x ∧ b.Defined (a.value x)
  | .parallel a b, x => a.Defined (left x) ∧ b.Defined (right x)

def Circuit.Rel {basis : Basis} {d n m : Nat} :
    Circuit basis d n m → StreamPoint d n → StreamPoint d m → Prop
  | .route f, x, y => y = x ∘ f
  | .constant q, _, y => y = ![Gimle.Asgard.Streams.constant basis q]
  | .axisVariable i, _, y => y = ![Gimle.Asgard.Streams.axisVariable basis i]
  | .unary op, x, y => y = ![op.value basis (x 0)]
  | .binary op, x, y => op.Domain basis (x 0) (x 1) ∧ y = ![op.value basis (x 0) (x 1)]
  | .compose a b, x, y => ∃ z, a.Rel x z ∧ b.Rel z y
  | .parallel a b, x, y => ∃ u v, a.Rel (left x) u ∧ b.Rel (right x) v ∧ y = append u v

theorem Circuit.rel_iff {basis : Basis} {d n m : Nat} (c : Circuit basis d n m)
    (x : StreamPoint d n) (y : StreamPoint d m) : c.Rel x y ↔ c.Defined x ∧ y = c.value x := by
  induction c with
  | route f => simp [Rel, Defined, value]
  | constant q => simp [Rel, Defined, value]
  | axisVariable i => simp [Rel, Defined, value]
  | unary op => simp [Rel, Defined, value]
  | binary op => rfl
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

def Circuit.pair {basis : Basis} {d n m o : Nat} (a : Circuit basis d n m)
    (b : Circuit basis d n o) : Circuit basis d n (m+o) :=
  .compose (.route (Fin.addCases id id)) (.parallel a b)

private theorem duplicate {d n : Nat} (x : StreamPoint d n) :
    x ∘ Fin.addCases id id = append x x := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j; simp [append]
  · intro j
    change x (Fin.addCases id id (j.natAdd n)) = Fin.addCases x x (j.natAdd n)
    rw [Fin.addCases_right, Fin.addCases_right]
    rfl

@[simp] theorem Circuit.pair_value {basis : Basis} {d n m o : Nat}
    (a : Circuit basis d n m) (b : Circuit basis d n o) (x : StreamPoint d n) :
    (a.pair b).value x = append (a.value x) (b.value x) := by
  simp [pair, value, duplicate]

@[simp] theorem Circuit.pair_defined {basis : Basis} {d n m o : Nat}
    (a : Circuit basis d n m) (b : Circuit basis d n o) (x : StreamPoint d n) :
    (a.pair b).Defined x ↔ a.Defined x ∧ b.Defined x := by
  simp [pair, Defined, value, duplicate]

inductive Expr (basis : Basis) (d n : Nat) where
  | input (i : Fin n)
  | constant (q : ℚ)
  | axisVariable (axis : Fin d)
  | unary (op : Unary d) (a : Expr basis d n)
  | binary (op : Binary d) (a b : Expr basis d n)
  deriving Repr, DecidableEq

def Expr.seriesCompose {basis : Basis} {d n : Nat} (axis : Fin d)
    (a b : Expr basis d n) := Expr.binary (.seriesCompose axis) a b

noncomputable def Expr.value {basis : Basis} {d n : Nat} (x : StreamPoint d n) :
    Expr basis d n → Stream d
  | .input i => x i
  | .constant q => Gimle.Asgard.Streams.constant basis q
  | .axisVariable i => Gimle.Asgard.Streams.axisVariable basis i
  | .unary op a => op.value basis (a.value x)
  | .binary op a b => op.value basis (a.value x) (b.value x)

def Expr.Defined {basis : Basis} {d n : Nat} (x : StreamPoint d n) : Expr basis d n → Prop
  | .input _ | .constant _ | .axisVariable _ => True
  | .unary _ a => a.Defined x
  | .binary op a b => (a.Defined x ∧ b.Defined x) ∧ op.Domain basis (a.value x) (b.value x)

def Expr.compile {basis : Basis} {d n : Nat} : Expr basis d n → Circuit basis d n 1
  | .input i => .route (fun _ => i)
  | .constant q => .compose (.route Fin.elim0) (.constant q)
  | .axisVariable i => .compose (.route Fin.elim0) (.axisVariable i)
  | .unary op a => .compose a.compile (.unary op)
  | .binary op a b => .compose (a.compile.pair b.compile) (.binary op)

@[simp] theorem Expr.compile_value {basis : Basis} {d n : Nat} (e : Expr basis d n)
    (x : StreamPoint d n) : e.compile.value x = ![e.value x] := by
  induction e with
  | input i => funext j; fin_cases j; rfl
  | constant q => rfl
  | axisVariable i => rfl
  | unary op a ha => simp [compile, Circuit.value, value, ha]
  | binary op a b ha hb =>
    simp [compile, Circuit.value, Circuit.pair_value, value, ha, hb]

@[simp] theorem Expr.compile_defined {basis : Basis} {d n : Nat} (e : Expr basis d n)
    (x : StreamPoint d n) : e.compile.Defined x ↔ e.Defined x := by
  induction e with
  | input i => rfl
  | constant q => simp [compile, Circuit.Defined, Defined]
  | axisVariable i => simp [compile, Circuit.Defined, Defined]
  | unary op a ha => simp [compile, Circuit.Defined, Defined, ha]
  | binary op a b ha hb =>
    simp [compile, Circuit.Defined, Circuit.pair_defined, Circuit.pair_value,
      compile_value, Defined, ha, hb]

theorem Expr.compile_rel {basis : Basis} {d n : Nat} (e : Expr basis d n)
    (x : StreamPoint d n) (y : StreamPoint d 1) :
    e.compile.Rel x y ↔ e.Defined x ∧ y = ![e.value x] := by
  rw [Circuit.rel_iff, compile_defined, compile_value]

#print axioms Circuit.rel_iff
#print axioms Expr.compile_value
#print axioms Expr.compile_defined
#print axioms Expr.compile_rel
end Gimle.Asgard.Streams
