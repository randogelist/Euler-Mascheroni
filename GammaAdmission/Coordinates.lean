import GammaAdmission.GammaRepresentative

/-!
# Finite GP–Kq–BKQR coordinates and fail-closed arithmetic checker

- X: representation dimension / number of polynomial coordinates.
- Y: tensor order (only Y=1 is accepted until a separate gamma reconstruction is proved).
- j: Kq resolution label.
- r: BKQR correction order label.
- K and R: actual finite dyadic integral envelope parameters.
- target: requested QIW denominator threshold.

All numeric evaluations in this module take place in `ℤ` and `ℚ`.
Nothing here is assumed to prove an analytic bound on gamma.
-/

namespace GammaAdmission

structure GammaCoord where
  X : ℕ
  Y : ℕ
  j : ℕ
  r : ℕ
  K : ℕ
  R : ℕ
  target : ℕ
  coeff : List ℤ
  B : ℤ
  deriving Repr

/-- C(1) for C(t)=sum (coeff[i] * t^(i+1)). -/
def GammaCoord.A (w : GammaCoord) : ℤ :=
  w.coeff.foldl (fun a c => a + c) 0

/-- C'(1). -/
def GammaCoord.derivAtOne (w : GammaCoord) : ℤ :=
  w.coeff.zipIdx.foldl
    (fun a ci => a + ci.1 * ((ci.2 + 1 : ℕ) : ℤ)) 0

/-- The rational harmonic readout associated with C. -/
def GammaCoord.readoutQ (w : GammaCoord) : ℚ :=
  w.coeff.zipIdx.foldl
    (fun a ci => a + (ci.1 : ℚ) *
      harmonicQ (2 ^ (ci.2 + 1) - 1)) 0

/-- P_r = sum of coefficients of t^j with j < r. -/
def GammaCoord.prefix (w : GammaCoord) (r : ℕ) : ℤ :=
  w.coeff.zipIdx.foldl
    (fun a ci => if ci.2 + 1 < r then a + ci.1 else a) 0

/-- Rising factorial m(m+1)...(m+ell), computed exactly as a natural. -/
def risingDenom (m ell : ℕ) : ℕ :=
  (Finset.range (ell + 1)).prod (fun t => m + t)

/-- Rational lower approximation to I_r = integral x^(2^r-1)/(1+x) dx. -/
def dyadicLower (r K : ℕ) : ℚ :=
  ∑ ell ∈ Finset.range K,
    (Nat.factorial ell : ℚ) /
      ((2 : ℚ) ^ (ell + 1) * (risingDenom (2 ^ r) ell : ℚ))

/-- Positive upper bound on I_r - dyadicLower r K. -/
def dyadicError (r K : ℕ) : ℚ :=
  (Nat.factorial K : ℚ) /
    ((2 : ℚ) ^ K * (risingDenom (2 ^ r) K : ℚ))

/-- Finite rational approximation of A*gamma-B. -/
def GammaCoord.base (w : GammaCoord) : ℚ :=
  ∑ t ∈ Finset.Icc 2 w.R,
    (w.prefix t : ℚ) * dyadicLower t w.K

/-- Lower endpoint. Negative coefficients pay their full certified error. -/
def GammaCoord.lower (w : GammaCoord) : ℚ :=
  w.base - ∑ t ∈ Finset.Icc 2 w.R,
    max (-(w.prefix t : ℚ)) 0 * dyadicError t w.K

/-- Upper endpoint. A>0 makes the omitted infinite tail positive. -/
def GammaCoord.upper (w : GammaCoord) : ℚ :=
  w.base +
    (∑ t ∈ Finset.Icc 2 w.R,
      max (w.prefix t : ℚ) 0 * dyadicError t w.K) +
    (w.A : ℚ) / ((2 : ℚ) ^ w.R)

/-- Exactly checkable arithmetic conditions, including the harmonic integer readout.
Y=1 prevents unproved tensor readouts from being substituted for gamma. -/
def GammaCoord.arithmeticReady (w : GammaCoord) : Prop :=
  w.X = w.coeff.length ∧
  0 < w.X ∧
  w.Y = 1 ∧
  w.r ≤ w.X ∧
  w.X ≤ w.R ∧
  0 < w.K ∧
  w.derivAtOne = 0 ∧
  0 < w.A ∧
  w.readoutQ = (w.B : ℚ)

/-- Exact rational sign test and requested QIW threshold.
The positive and negative cases are both supported. -/
def GammaCoord.intervalGuard (w : GammaCoord) : Prop :=
  (0 < w.lower ∧ w.upper < (1 : ℚ) / (w.target + 1 : ℕ)) ∨
  (w.upper < 0 ∧ -w.lower < (1 : ℚ) / (w.target + 1 : ℕ))

/-- Validity is a finite proposition decidable in exact rational arithmetic. -/
def GammaCoord.ValidRaw (w : GammaCoord) : Prop :=
  w.arithmeticReady ∧ w.intervalGuard

/-- All arithmetic clauses are evaluated individually to avoid deep
`Decidable` instance synthesis for the nested conjunction. No `classical`
decision procedure is used by the executable checker. -/
def GammaCoord.arithmeticCheck (w : GammaCoord) : Bool :=
  decide (w.X = w.coeff.length) &&
  decide (0 < w.X) &&
  decide (w.Y = 1) &&
  decide (w.r ≤ w.X) &&
  decide (w.X ≤ w.R) &&
  decide (0 < w.K) &&
  decide (w.derivAtOne = 0) &&
  decide (0 < w.A) &&
  decide (w.readoutQ = (w.B : ℚ))

/-- Exact reflection of the arithmetic Boolean clauses. -/
theorem GammaCoord.arithmeticCheck_iff (w : GammaCoord) :
    w.arithmeticCheck = true ↔ w.arithmeticReady := by
  -- Bool.and groups the atomic checks to the left; the Prop was written
  -- right-associatively. This is propositional associativity only.
  -- `tauto` closes the resulting equivalence without changing either predicate.
  simp [GammaCoord.arithmeticCheck, GammaCoord.arithmeticReady] <;> tauto

/-- Both rational sign branches of the nonzero QIW interval. -/
def GammaCoord.intervalCheck (w : GammaCoord) : Bool :=
  (decide (0 < w.lower) &&
    decide (w.upper < (1 : ℚ) / (w.target + 1 : ℕ))) ||
  (decide (w.upper < 0) &&
    decide (-w.lower < (1 : ℚ) / (w.target + 1 : ℕ)))

/-- Exact reflection of the interval Boolean clauses. -/
theorem GammaCoord.intervalCheck_iff (w : GammaCoord) :
    w.intervalCheck = true ↔ w.intervalGuard := by
  simp [GammaCoord.intervalCheck, GammaCoord.intervalGuard]

/-- Fail-closed checker: all clauses run in finite integer/rational arithmetic. -/
def checkRaw (w : GammaCoord) : Bool :=
  w.arithmeticCheck && w.intervalCheck

/-- Reflection of the Boolean checker, a purely arithmetic statement. -/
theorem checkRaw_iff (w : GammaCoord) :
    checkRaw w = true ↔ w.ValidRaw := by
  simp [checkRaw, GammaCoord.arithmeticCheck_iff,
    GammaCoord.intervalCheck_iff, GammaCoord.ValidRaw]

/-- The real linear form is noncomputable because native gamma is. -/
noncomputable def GammaCoord.gammaLinear (w : GammaCoord) : ℝ :=
  linearForm gamma w.A w.B


/-- A rational QIW threshold becomes the corresponding real threshold.

This avoids an implicit cast across rational division.  First multiply by
`N+1 > 0` in `ℚ`, then cast the polynomial inequality to `ℝ`, and divide
again there.  Pure arithmetic: no gamma or analytic hypothesis is involved. -/
theorem rational_cutoff_cast (a : ℚ) (N : ℕ)
    (h : a < (1 : ℚ) / (N + 1 : ℕ)) :
    (a : ℝ) < 1 / ((N : ℝ) + 1) := by
  have hdq : (0 : ℚ) < ((N + 1 : ℕ) : ℚ) := by positivity
  have hmulQ : a * ((N + 1 : ℕ) : ℚ) < 1 :=
    (lt_div_iff₀ hdq).mp h
  have hmulR : (a : ℝ) * ((N : ℝ) + 1) < 1 := by
    exact_mod_cast hmulQ
  exact (lt_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr hmulR

end GammaAdmission
