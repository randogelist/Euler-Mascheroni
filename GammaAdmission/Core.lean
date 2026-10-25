import Mathlib

/-!
# Universal integer-linear-form soundness

This file is independent of Euler's constant and of the GP/Kq/BKQR models.
No irrationality hypothesis is used. No `sorry` or custom axiom is present.
-/

namespace GammaAdmission

/-- The exact integer linear form associated with a real number. -/
def linearForm (alpha : ℝ) (A B : ℤ) : ℝ :=
  (A : ℝ) * alpha - (B : ℝ)

/-- Arbitrarily small, nonzero integer linear forms force irrationality. -/
theorem irrational_of_arbitrarily_small_forms (alpha : ℝ)
    (h : ∀ eps : ℝ, 0 < eps →
      ∃ A B : ℤ, 0 < |linearForm alpha A B| ∧
        |linearForm alpha A B| < eps) : Irrational alpha := by
  apply (irrational_iff_ne_rational alpha).2
  intro p q hq hpq
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hqabs : 0 < |(q : ℝ)| := abs_pos.mpr hqR
  obtain ⟨A, B, hpos, hsmall⟩ := h (1 / |(q : ℝ)|) (one_div_pos.mpr hqabs)
  have hmul : linearForm alpha A B * (q : ℝ) =
      ((A * p - B * q : ℤ) : ℝ) := by
    rw [linearForm, hpq]
    field_simp [hqR]
    push_cast
    ring
  have habs : |linearForm alpha A B| * |(q : ℝ)| =
      |((A * p - B * q : ℤ) : ℝ)| := by
    have h0 := congrArg (fun z : ℝ => |z|) hmul
    simpa only [abs_mul] using h0
  have hnum : A * p - B * q ≠ 0 := by
    intro hz
    have hh : 0 < |((A * p - B * q : ℤ) : ℝ)| := by
      rw [← habs]
      exact mul_pos hpos hqabs
    simp [hz] at hh
  have hIntAbsPos : (0 : ℤ) < |A * p - B * q| :=
    abs_pos.mpr hnum
  have hinteger : (1 : ℤ) ≤ |A * p - B * q| := by omega
  have hgap : (1 : ℝ) ≤ |((A * p - B * q : ℤ) : ℝ)| := by
    exact_mod_cast hinteger
  have hsmallmul : |linearForm alpha A B| * |(q : ℝ)| < 1 := by
    calc
      |linearForm alpha A B| * |(q : ℝ)|
          < (1 / |(q : ℝ)|) * |(q : ℝ)| :=
              mul_lt_mul_of_pos_right hsmall hqabs
      _ = 1 := by field_simp [ne_of_gt hqabs]
  rw [habs] at hsmallmul
  linarith

/-- Quantified finite witnesses (one at every requested precision) imply irrationality. -/
theorem irrational_of_qiw (alpha : ℝ)
    (h : ∀ N : ℕ, ∃ A B : ℤ,
      0 < |linearForm alpha A B| ∧
      |linearForm alpha A B| < 1 / ((N : ℝ) + 1)) :
    Irrational alpha := by
  apply irrational_of_arbitrarily_small_forms alpha
  intro eps heps
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / eps)
  have hNpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hbound : (1 : ℝ) / ((N : ℝ) + 1) < eps := by
    have h1 : (1 : ℝ) < eps * (N : ℝ) := by
      simpa only [mul_comm] using (div_lt_iff₀ heps).mp hN
    have h2 : (1 : ℝ) < eps * ((N : ℝ) + 1) := by
      nlinarith
    exact (div_lt_iff₀ hNpos).2 (by simpa [mul_comm] using h2)
  obtain ⟨A, B, hpos, hsmall⟩ := h N
  exact ⟨A, B, hpos, lt_trans hsmall hbound⟩

end GammaAdmission
