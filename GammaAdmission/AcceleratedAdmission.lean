import GammaAdmission.AcceleratedBinet
import GammaAdmission.Core

/-!
# Binet accelerated one-coordinate admission

The arithmetic checker is closed and finite. GammaBinetBoundsSound is the
independent analytic theorem still to be proved from Binet's formula,
Bernoulli moments, and native Mathlib gamma. The successor is also open.
Neither is a boolean inside raw witness data.
-/

namespace GammaAdmission

/-- Open mathematical bridge: Binet bounds hold for every admitted packet.
This is a theorem obligation, not a constructed value or an axiom. -/
structure GammaBinetBoundsSound : Prop where
  enclosure : ∀ w : GammaBinetCoord, w.arithmeticReady →
    (w.lower : ℝ) ≤ w.packet.gammaLinear ∧
    w.packet.gammaLinear ≤ (w.upper : ℝ)

/-- Once the analytic bounds theorem is proved, every passing packet is
an independently sound, nonzero, finite integer-linear-form witness. -/
theorem accepted_binet_sound
    (bridge : GammaBinetBoundsSound)
    (w : GammaBinetCoord) (hw : checkBinet w = true) :
    0 < |w.packet.gammaLinear| ∧
      |w.packet.gammaLinear| < 1 / ((w.packet.target : ℝ) + 1) := by
  obtain ⟨harith, hguard⟩ := (checkBinet_iff w).mp hw
  obtain ⟨hl, hu⟩ := bridge.enclosure w harith
  rcases hguard with ⟨hlo, hhi⟩ | ⟨hhi, hlo⟩
  · have hpos : 0 < w.packet.gammaLinear := by
      have hposlo : (0 : ℝ) < (w.lower : ℝ) := by exact_mod_cast hlo
      exact lt_of_lt_of_le hposlo hl
    have hhiR : (w.upper : ℝ) < 1 / ((w.packet.target : ℝ) + 1) :=
      rational_cutoff_cast w.upper w.packet.target hhi
    have hsmall : w.packet.gammaLinear < 1 / ((w.packet.target : ℝ) + 1) :=
      lt_of_le_of_lt hu hhiR
    simpa [abs_of_pos hpos] using And.intro hpos hsmall
  · have hneg : w.packet.gammaLinear < 0 := by
      have hnegup : (w.upper : ℝ) < 0 := by exact_mod_cast hhi
      exact lt_of_le_of_lt hu hnegup
    have hloR : -(w.lower : ℝ) < 1 / ((w.packet.target : ℝ) + 1) := by
      simpa only [Rat.cast_neg] using
        (rational_cutoff_cast (-w.lower) w.packet.target hlo)
    have hsmall : -w.packet.gammaLinear < 1 / ((w.packet.target : ℝ) + 1) :=
      lt_of_le_of_lt (neg_le_neg hl) hloR
    have hpos : 0 < -w.packet.gammaLinear := neg_pos.mpr hneg
    simpa [abs_of_neg hneg] using And.intro hpos hsmall

/-- The global Riesz successor is *not* created by finite admission.
It must be proved to preserve the fast checker and increase the grade. -/
structure GammaBinetSuccessor where
  next : GammaBinetCoord → GammaBinetCoord
  closed : ∀ w : GammaBinetCoord, checkBinet w = true →
    checkBinet (next w) = true
  target_step : ∀ w : GammaBinetCoord, checkBinet w = true →
    (next w).packet.target = w.packet.target + 1

theorem GammaBinetSuccessor.checked_iter (E : GammaBinetSuccessor)
    (w : GammaBinetCoord) (hw : checkBinet w = true) (k : ℕ) :
    checkBinet ((E.next^[k]) w) = true := by
  induction k with
  | zero => simpa using hw
  | succ k hk =>
      rw [Function.iterate_succ_apply']
      exact E.closed _ hk

theorem GammaBinetSuccessor.target_iter (E : GammaBinetSuccessor)
    (w : GammaBinetCoord) (hw : checkBinet w = true) (k : ℕ) :
    ((E.next^[k]) w).packet.target = w.packet.target + k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', E.target_step _ (E.checked_iter w hw k)]
      omega

/-- Final accelerated QIW endpoint. Conditional on TWO independent global
proofs. A finite `checkBinet = true` is not sufficient by itself. -/
theorem GAMMA_IRRATIONAL_OF_ACCELERATED_ONE_COORDINATE
    (bridge : GammaBinetBoundsSound)
    (E : GammaBinetSuccessor)
    (h : ∃ w : GammaBinetCoord, checkBinet w = true) :
    Irrational Real.eulerMascheroniConstant := by
  obtain ⟨w, hw⟩ := h
  apply irrational_of_qiw gamma
  intro N
  let wk : GammaBinetCoord := (E.next^[N]) w
  have hwk : checkBinet wk = true := E.checked_iter w hw N
  have hg : wk.packet.target = w.packet.target + N := E.target_iter w hw N
  obtain ⟨hpos, hsmall⟩ := accepted_binet_sound bridge wk hwk
  have hNat : N ≤ wk.packet.target := by omega
  have hReal : (N : ℝ) + 1 ≤ (wk.packet.target : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hNat 1
  have hfrac : (1 : ℝ) / ((wk.packet.target : ℝ) + 1) ≤
      1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) hReal
  exact ⟨wk.packet.A, wk.packet.B, hpos, lt_of_lt_of_le hsmall hfrac⟩

end GammaAdmission
