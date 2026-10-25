import GammaAdmission.Coordinates

/-!
# Accelerated Binet / Stieltjes coordinate checking (finite rational layer)

Instead of bounding each dyadic GP cell, expand the Binet Stieltjes
kernel to an arbitrary *certified finite* Bernoulli order. This produces
rational enclosure candidates in O(X*p) arithmetic operations.

Important trust boundary: the analytic theorem showing that the interval
contains native `Real.eulerMascheroniConstant` is NOT asserted here.
The finite checker never accepts an analytic proof flag from input.

Our pre-verified coefficient table is beta_m = |B_(2m)|/(2m), m=1..7.
Orders p<=6 have valid p+1 remainder coefficient.
-/

namespace GammaAdmission

/-- Exact polynomial C(z) = sum_i coeff[i] z^(i+1). -/
def GammaCoord.polyEval (w : GammaCoord) (z : ℚ) : ℚ :=
  w.coeff.zipIdx.foldl
    (fun a ci => a + (ci.1 : ℚ) * z ^ (ci.2 + 1)) 0

/-- Rational Bernoulli integral coefficients, valid for 1 <= m <= 7.
The final zero is a fail-closed out-of-range placeholder; a packet
must check `p <= 6` before its enclosure is admitted. -/
def binetBeta : ℕ → ℚ
  | 1 => 1 / 12
  | 2 => 1 / 120
  | 3 => 1 / 252
  | 4 => 1 / 240
  | 5 => 1 / 132
  | 6 => 691 / 32760
  | 7 => 1 / 12
  | _ => 0

/-- Alternating sign of the Bernoulli/Stieltjes expansion. -/
def binetSign (m : ℕ) : ℚ :=
  if m % 2 = 1 then 1 else -1

/-- An acceleration packet reuses every coordinate of the original checker,
with a new Bernoulli expansion order `p`. X and Y remain independent axes.
The currently verified gamma readout only admits Y=1. -/
structure GammaBinetCoord where
  packet : GammaCoord
  p : ℕ
  deriving Repr

/-- Rational center of the p-th finite Binet expansion. -/
def GammaBinetCoord.center (w : GammaBinetCoord) : ℚ :=
  (1 / 2 : ℚ) * w.packet.polyEval (1 / 2) +
    ∑ m ∈ Finset.Icc 1 w.p,
      binetSign m * binetBeta m *
        w.packet.polyEval ((1 : ℚ) / ((4 : ℚ) ^ m))

/-- Symmetric rigorous candidate remainder radius.
Its real analytic validity is a separately formalized theorem obligation. -/
def GammaBinetCoord.radius (w : GammaBinetCoord) : ℚ :=
  binetBeta (w.p + 1) *
    w.packet.coeff.zipIdx.foldl
      (fun acc ci => acc + |(ci.1 : ℚ)| /
         ((4 : ℚ) ^ ((ci.2 + 1) * (w.p + 1)))) 0

def GammaBinetCoord.lower (w : GammaBinetCoord) : ℚ :=
  w.center - w.radius

def GammaBinetCoord.upper (w : GammaBinetCoord) : ℚ :=
  w.center + w.radius

/-- Optional BKQR moment cancellation. If r=0 it is vacuous; otherwise
check the half-mode and each of the finitely many even Stieltjes modes. -/
def GammaBinetCoord.cancellationCheck (w : GammaBinetCoord) : Bool :=
  decide (w.packet.r = 0) ||
    (decide (w.packet.polyEval (1 / 2) = 0) &&
      (List.range w.packet.r).all
        (fun k => decide (w.packet.polyEval
          ((1 : ℚ) / ((4 : ℚ) ^ (k + 1))) = 0)))

/-- Its executable Boolean is part of the finite certificate predicate. -/
def GammaBinetCoord.cancellationReady (w : GammaBinetCoord) : Prop :=
  w.cancellationCheck = true

/-- Finite exact-arithmetic admission conditions.
The input does NOT provide either interval endpoint or an analytic proof. -/
def GammaBinetCoord.arithmeticReady (w : GammaBinetCoord) : Prop :=
  w.packet.arithmeticReady ∧
  w.p ≤ 6 ∧
  w.packet.r ≤ w.p ∧
  w.cancellationReady

def GammaBinetCoord.intervalGuard (w : GammaBinetCoord) : Prop :=
  (0 < w.lower ∧ w.upper < (1 : ℚ) / (w.packet.target + 1 : ℕ)) ∨
  (w.upper < 0 ∧ -w.lower < (1 : ℚ) / (w.packet.target + 1 : ℕ))

def GammaBinetCoord.Valid (w : GammaBinetCoord) : Prop :=
  w.arithmeticReady ∧ w.intervalGuard

/-- Explicit Boolean clauses avoid deep `Decidable` instance search. -/
def GammaBinetCoord.arithmeticCheck (w : GammaBinetCoord) : Bool :=
  w.packet.arithmeticCheck &&
  decide (w.p ≤ 6) &&
  decide (w.packet.r ≤ w.p) &&
  w.cancellationCheck

theorem GammaBinetCoord.arithmeticCheck_iff (w : GammaBinetCoord) :
    w.arithmeticCheck = true ↔ w.arithmeticReady := by
  simp [GammaBinetCoord.arithmeticCheck,
    GammaBinetCoord.arithmeticReady,
    GammaBinetCoord.cancellationReady,
    GammaCoord.arithmeticCheck_iff] <;> tauto

def GammaBinetCoord.intervalCheck (w : GammaBinetCoord) : Bool :=
  (decide (0 < w.lower) &&
    decide (w.upper < (1 : ℚ) / (w.packet.target + 1 : ℕ))) ||
  (decide (w.upper < 0) &&
    decide (-w.lower < (1 : ℚ) / (w.packet.target + 1 : ℕ)))

theorem GammaBinetCoord.intervalCheck_iff (w : GammaBinetCoord) :
    w.intervalCheck = true ↔ w.intervalGuard := by
  simp [GammaBinetCoord.intervalCheck, GammaBinetCoord.intervalGuard]

/-- Untrusted numeric packet -> checkable Bool. Fail closed. -/
def checkBinet (w : GammaBinetCoord) : Bool :=
  w.arithmeticCheck && w.intervalCheck

/-- Exact reflection of the finite checker, no analytic or arithmetic axioms. -/
theorem checkBinet_iff (w : GammaBinetCoord) :
    checkBinet w = true ↔ w.Valid := by
  -- Keep the same explicit conjunction normalization as `checkRaw_iff`.
  simp [checkBinet, GammaBinetCoord.Valid,
    GammaBinetCoord.arithmeticCheck_iff,
    GammaBinetCoord.intervalCheck_iff]

end GammaAdmission
