import GammaAdmission.Core

/-!
# Generator-independent endpoint: analytic rational series and one coordinate

This file is reusable for e, sqrt(2), gamma, etc. It does not assume any of
them irrational. An `AnalyticPowerSeriesInput` is evidence of identification,
not of irrationality. A `RieszEngine` needs a separately established global
successor and shrinking-error theorem.
-/

namespace GammaAdmission
open Filter

/-- One genuine rational-coefficient power-series representation of `alpha`. -/
structure AnalyticPowerSeriesInput (alpha : ℝ) where
  coeff : ℕ → ℚ
  hasSum : HasSum (fun n : ℕ => (coeff n : ℝ)) alpha

/-- One complete abstract coordinate engine with an admitted successor orbit. -/
structure RieszEngine (alpha : ℝ) where
  Coord : Type
  check : Coord → Bool
  next : Coord → Coord
  A : Coord → ℤ
  B : Coord → ℤ
  upper : Coord → ℚ
  closed : ∀ w, check w = true → check (next w) = true
  sound : ∀ w, check w = true →
    0 < |linearForm alpha (A w) (B w)| ∧
    |linearForm alpha (A w) (B w)| ≤ (upper w : ℝ)
  decay : ∀ w, check w = true →
    Filter.Tendsto
      (fun k : ℕ => (upper ((next^[k]) w) : ℝ))
      Filter.atTop (nhds 0)

/-- Admit one coordinate and get arbitrarily small integer linear forms. -/
theorem RieszEngine.one_entry (alpha : ℝ) (E : RieszEngine alpha)
    (h : ∃ w : E.Coord, E.check w = true) : Irrational alpha := by
  obtain ⟨w, hw⟩ := h
  have hiter : ∀ k : ℕ, E.check ((E.next^[k]) w) = true := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact E.closed _ ih
  apply irrational_of_arbitrarily_small_forms alpha
  intro eps heps
  have hEv : ∀ᶠ k : ℕ in Filter.atTop,
      (E.upper ((E.next^[k]) w) : ℝ) < eps :=
    (E.decay w hw).eventually (isOpen_Iio.mem_nhds heps)
  obtain ⟨k, hk⟩ := hEv.exists
  obtain ⟨hpos, hbound⟩ := E.sound _ (hiter k)
  exact ⟨E.A ((E.next^[k]) w), E.B ((E.next^[k]) w),
    hpos, lt_of_le_of_lt hbound hk⟩

/-- Generic desired endpoint: analytic input and one admitted coordinate. -/
theorem IRRATIONAL_OF_ANALYTIC_INPUT_AND_ONE_COORDINATE
    (alpha : ℝ) (_R : AnalyticPowerSeriesInput alpha)
    (E : RieszEngine alpha)
    (h : ∃ w : E.Coord, E.check w = true) :
    Irrational alpha :=
  RieszEngine.one_entry alpha E h

end GammaAdmission
