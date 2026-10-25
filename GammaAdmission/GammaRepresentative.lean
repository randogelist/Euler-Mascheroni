import GammaAdmission.Core
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Euler–Mascheroni: native target and rational Kq coefficients

`gamma` is the existing Mathlib constant. The rational dyadic series is a
candidate analytic representative. Its telescoping identity is purely algebraic;
identifying its limit with `gamma` is a separate analytical theorem obligation.
-/

namespace GammaAdmission

noncomputable abbrev gamma : ℝ := Real.eulerMascheroniConstant

/-- Native Mathlib harmonic-minus-log characterization, no new axiom. -/
theorem gamma_native_harmonic_limit :
    Filter.Tendsto
      (fun n : ℕ => (harmonic n : ℝ) - Real.log (n : ℝ))
      Filter.atTop (nhds gamma) :=
  Real.tendsto_harmonic_sub_log

/-- Finite rational harmonic sum; index `n` means the sum from 1 through `n`. -/
def harmonicQ (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, (1 : ℚ) / (j + 1 : ℕ)

/-- A rational Kq expression with the logarithmic scale term canceled. -/
def kqRational (n : ℕ) : ℚ :=
  (n + 1 : ℕ) * harmonicQ (2 ^ n - 1) -
    (n : ℕ) * harmonicQ (2 ^ (n + 1) - 1)

/-- Rational coefficients of the telescoping Kq power series. -/
def gammaCoeff : ℕ → ℚ
  | 0 => kqRational 1
  | n + 1 => kqRational (n + 2) - kqRational (n + 1)

/-- Finite sums telescope exactly, in rational arithmetic. -/
theorem gammaCoeff_partial_sum (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), gammaCoeff k) =
      kqRational (n + 1) := by
  induction n with
  | zero => simp [gammaCoeff]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [gammaCoeff]
      ring

/-- The analytic series/limit identification still to be established in Lean.
It is *not* a definition of irrationality and supplies no arithmetic witness. -/
structure GammaSeriesIdentification : Prop where
  dyadic_tendsto_gamma :
    Filter.Tendsto (fun n : ℕ => (kqRational (n + 1) : ℝ))
      Filter.atTop (nhds gamma)

/-- The actual dyadic coefficient map. This is data, not a proven identity. -/
def gammaRationalSeriesCoeff : ℕ → ℚ := gammaCoeff

end GammaAdmission
