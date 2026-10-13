import Gimle.Asgard.Streams.VorticityTable

/-! # The vorticity stream from three cosine modes

The two-dimensional Euler and Navier–Stokes equations on the torus, as the
formal vorticity stream of `Streams.NS`, from the initial vorticity

  `ω₀ = cos x + cos(x + y) + cos(2x + y)`

— the three modes of forseti-lean's Galerkin member `T3` (unforced here), each
with amplitude one, so `1/2` on each of `±(1,0), ±(1,1), ±(2,1)` in
exponential coordinates.
`stream_coeff` turns a coefficient of the stream into a rational the kernel
computes from the table of the start, and `decide +kernel` checks each value
below; nothing is imported from outside Lean. The series is exact and unique
(`NS.formal_unique`); nothing about its convergence is claimed here.

At `t¹` the Euler stream already carries `cos y`, a mode the three-mode
Galerkin truncation discards, with coefficient `1/8` on `±(0,1)`; `(2,2)` is
absent at `t¹` and present at `t²`. At `t¹` the viscous stream (`ν = 1/10`)
is the Euler coefficient plus the decay `−ν|k|² ω₀_k` of each initial mode:
the `(2,1)` coefficient moves from `−1/8` to `−1/8 − ν·5·(1/2) = −3/8`, and a
mode absent from `ω₀` has no decay term at `t¹`. From `t²` on the values
differ non-additively. -/
namespace Gimle.Asgard.Examples.EulerThreeMode

open Gimle.Asgard.Streams Gimle.Asgard.Streams.Torus Gimle.Asgard.Streams.NS

/-- The start as a table: `1/2` on each of the six modes. -/
def startTable : Table :=
  [((1, 0), 1 / 2), ((-1, 0), 1 / 2), ((1, 1), 1 / 2), ((-1, -1), 1 / 2),
    ((2, 1), 1 / 2), ((-2, -1), 1 / 2)]

/-- `ω₀ = cos x + cos(x + y) + cos(2x + y)`. -/
noncomputable def ω₀ : TrigPoly := cosine (1, 0) + cosine (1, 1) + cosine (2, 1)

/-- The boundary stream: `ω₀` at `t⁰`; nothing else of it is read. -/
noncomputable def start : TrigStream := fun _ => ω₀

theorem start_eq_table : Table.toTrig startTable = start 0 := by
  simp only [start, ω₀, cosine, startTable, Table.toTrig, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero, Prod.neg_mk, neg_zero, Int.reduceNeg]
  abel

/-- The start, as the table. -/
theorem ω₀_eq_table : ω₀ = Table.toTrig startTable := start_eq_table.symm

theorem ω₀_isEven : IsEven ω₀ :=
  isEven_add (isEven_add (isEven_cosine _) (isEven_cosine _)) (isEven_cosine _)

theorem ω₀_meanZero : MeanZero ω₀ :=
  meanZero_add (meanZero_add (meanZero_cosine (by decide)) (meanZero_cosine (by decide)))
    (meanZero_cosine (by decide))

/-- Every coefficient of either stream is even and mean zero. -/
theorem coeff_isEven (ν : ℚ) (n : ℕ) : IsEven (stream .ogf ν start n) :=
  NS.stream_isEven .ogf ν ω₀_isEven n

theorem coeff_meanZero (ν : ℚ) (n : ℕ) : MeanZero (stream .ogf ν start n) :=
  NS.stream_meanZero .ogf ν ω₀_meanZero n

/-! ## Euler: `ν = 0` -/

/-- `[t¹ · e^{i x}] = −3/40`. -/
theorem euler_t_x : stream .ogf 0 start 1 (1, 0) = -3 / 40 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-- `[t¹ · e^{i y}] = 1/8`: a mode the start does not have. -/
theorem euler_t_y : stream .ogf 0 start 1 (0, 1) = 1 / 8 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-- `[t¹ · e^{i (x+y)}] = 1/5`. -/
theorem euler_t_xy : stream .ogf 0 start 1 (1, 1) = 1 / 5 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-- `[t¹ · e^{i (2x+y)}] = −1/8`: pure transport, no decay. -/
theorem euler_t_2xy : stream .ogf 0 start 1 (2, 1) = -1 / 8 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-- `[t¹ · e^{i (3x+2y)}] = 3/40`: a mode the first step creates. -/
theorem euler_t_3x2y : stream .ogf 0 start 1 (3, 2) = 3 / 40 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-- `(2, 2)` is not reached at `t¹` … -/
theorem euler_t_2x2y : stream .ogf 0 start 1 (2, 2) = 0 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-- … and is at `t²`: `11/130`. -/
theorem euler_t2_2x2y : stream .ogf 0 start 2 (2, 2) = 11 / 130 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-- `[t² · e^{i (x+y)}] = −49/1300`. -/
theorem euler_t2_xy : stream .ogf 0 start 2 (1, 1) = -49 / 1300 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-- `[t³ · e^{i x}] = 27/32000`. -/
theorem euler_t3_x : stream .ogf 0 start 3 (1, 0) = 27 / 32000 := by
  rw [stream_coeff 0 startTable start start_eq_table]; decide +kernel

/-! ## Navier–Stokes: `ν = 1/10` -/

/-- The viscosity of the viscous example. -/
def ν : ℚ := 1 / 10

/-- `[t¹ · e^{i (2x+y)}] = −3/8`: the transport's `−1/8` and the decay `−ν·5/2`. -/
theorem viscous_t_2xy : stream .ogf ν start 1 (2, 1) = -3 / 8 := by
  rw [stream_coeff ν startTable start start_eq_table]; decide +kernel

/-- `[t¹ · e^{i y}] = 1/8`: a mode absent from `ω₀` has no decay term at `t¹`. -/
theorem viscous_t_y : stream .ogf ν start 1 (0, 1) = 1 / 8 := by
  rw [stream_coeff ν startTable start start_eq_table]; decide +kernel

/-- `[t² · e^{i (x+y)}] = −7/65`. -/
theorem viscous_t2_xy : stream .ogf ν start 2 (1, 1) = -7 / 65 := by
  rw [stream_coeff ν startTable start start_eq_table]; decide +kernel

/-- `[t² · e^{i (2x+2y)}] = 11/130`, as for Euler, for this start: every pair
reaching `(2,2)` at `t²` pairs `ω₀` with a `t¹` mode absent from `ω₀`, whose
`t¹` coefficient is `ν`-independent. -/
theorem viscous_t2_2x2y : stream .ogf ν start 2 (2, 2) = 11 / 130 := by
  rw [stream_coeff ν startTable start start_eq_table]; decide +kernel

/-! ## Uniqueness -/

/-- Any formal stream solving the Euler equation from `ω₀` is this one. -/
theorem unique (a : TrigStream) (pde : TrigStream.derivative .ogf a = rhs .ogf 0 a)
    (slice : a 0 = ω₀) : a = stream .ogf 0 start :=
  eq_stream .ogf 0 start a pde slice

#print axioms euler_t_x
#print axioms euler_t3_x
#print axioms viscous_t2_xy
#print axioms unique
end Gimle.Asgard.Examples.EulerThreeMode
