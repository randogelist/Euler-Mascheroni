import Endpoint622

/-!
# A finite-width obstruction for the fixed-order Binet checker

This file concerns the rational checker only. Its conclusions require neither
the analytic gamma bridge nor irrationality. Unbounded declared dimension is
a necessary condition; padding with zeros does not make it sufficient.
-/

namespace GammaAdmission

theorem weighted_fold_lower (coeff : List ℤ) (p : ℕ)
    (hpos : 0 < coeff.foldl (fun a c => a + c) 0)
    (hp : p ≤ 6) :
    (1 : ℚ) / 4 ^ (7 * coeff.length) ≤
      coeff.zipIdx.foldl
        (fun a ci => a + |(ci.1 : ℚ)| / 4 ^ ((ci.2 + 1) * (p + 1))) 0 := by
  let weight : ℤ × ℕ → ℚ := fun ci =>
    |(ci.1 : ℚ)| / 4 ^ ((ci.2 + 1) * (p + 1))
  have hs : 0 < coeff.sum := by
    simpa only [List.sum_eq_foldl] using hpos
  have hex : ∃ c ∈ coeff, (0 : ℤ) < c :=
    List.exists_lt_of_sum_lt (l := coeff) (fun _ => (0 : ℤ)) id (by simpa using hs)
  obtain ⟨c, hc, hcp⟩ := hex
  have hcm : c ∈ coeff.zipIdx.map Prod.fst := by
    simpa only [List.zipIdx_map_fst] using hc
  obtain ⟨ci, hci, hceq⟩ := List.mem_map.mp hcm
  have hi : ci.2 < coeff.length := by
    simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hci
  have hc1 : (1 : ℤ) ≤ ci.1 := by omega
  have hc1Q : (1 : ℚ) ≤ (ci.1 : ℚ) := by exact_mod_cast hc1
  have habs : (1 : ℚ) ≤ |(ci.1 : ℚ)| := le_trans hc1Q (le_abs_self _)
  have hexp : (ci.2 + 1) * (p + 1) ≤ 7 * coeff.length := by nlinarith
  have hden : (4 : ℚ) ^ ((ci.2 + 1) * (p + 1)) ≤ 4 ^ (7 * coeff.length) :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hweight : (1 : ℚ) / 4 ^ (7 * coeff.length) ≤ weight ci := by
    dsimp [weight]
    calc
      (1 : ℚ) / 4 ^ (7 * coeff.length)
          ≤ 1 / 4 ^ ((ci.2 + 1) * (p + 1)) :=
        one_div_le_one_div_of_le (by positivity) hden
      _ ≤ |(ci.1 : ℚ)| / 4 ^ ((ci.2 + 1) * (p + 1)) :=
        div_le_div_of_nonneg_right habs (by positivity)
  have hnonneg : ∀ x ∈ coeff.zipIdx.map weight, (0 : ℚ) ≤ x := by
    intro x hx
    obtain ⟨cj, _, rfl⟩ := List.mem_map.mp hx
    dsimp [weight]
    positivity
  have hsingle : weight ci ≤ (coeff.zipIdx.map weight).sum :=
    List.single_le_sum hnonneg (weight ci) (List.mem_map.mpr ⟨ci, hci, rfl⟩)
  have hfold : (coeff.zipIdx.map weight).sum =
      coeff.zipIdx.foldl
        (fun a ci => a + |(ci.1 : ℚ)| / 4 ^ ((ci.2 + 1) * (p + 1))) 0 := by
    rw [List.sum_eq_foldl, List.foldl_map]
  exact hfold ▸ le_trans hweight hsingle

theorem binetBeta_lower {p : ℕ} (hp : p ≤ 6) :
    (1 : ℚ) / 252 ≤ binetBeta (p + 1) := by
  interval_cases p <;> norm_num [binetBeta]

/-- A sign-separated symmetric interval has width below the requested cutoff. -/
theorem valid_radius_lt_cutoff (w : GammaBinetCoord) (hw : w.Valid) :
    2 * w.radius < (1 : ℚ) / (w.packet.target + 1 : ℕ) := by
  rcases hw.2 with hpos | hneg
  · rcases hpos with ⟨hl, hu⟩
    unfold GammaBinetCoord.lower at hl
    unfold GammaBinetCoord.upper at hu
    linarith
  · rcases hneg with ⟨hu, hl⟩
    unfold GammaBinetCoord.lower at hl
    unfold GammaBinetCoord.upper at hu
    linarith

/-- Every arithmetically admissible packet has a positive remainder-radius floor. -/
theorem arithmetic_radius_lower (w : GammaBinetCoord)
    (hw : w.arithmeticReady) :
    (1 : ℚ) / (252 * 4 ^ (7 * w.packet.X)) ≤ w.radius := by
  rcases hw with ⟨harith, hp, _, _⟩
  rcases harith with ⟨hX, _, _, _, _, _, _, hA, _⟩
  have hfold := weighted_fold_lower w.packet.coeff w.p hA hp
  have hbeta := binetBeta_lower hp
  have hbeta0 : (0 : ℚ) ≤ binetBeta (w.p + 1) := by linarith
  rw [hX]
  unfold GammaBinetCoord.radius
  calc
    (1 : ℚ) / (252 * 4 ^ (7 * w.packet.coeff.length)) =
        ((1 : ℚ) / 252) * ((1 : ℚ) / 4 ^ (7 * w.packet.coeff.length)) := by
      simp only [one_div, mul_inv_rev]
      ring
    _ ≤ _ := mul_le_mul hbeta hfold (by positivity) hbeta0

/-- At fixed declared dimension the current finite-order checker has bounded targets. -/
theorem valid_target_bound (w : GammaBinetCoord) (hw : w.Valid) :
    w.packet.target + 1 < 126 * 4 ^ (7 * w.packet.X) := by
  have hr := arithmetic_radius_lower w hw.1
  have hg := valid_radius_lt_cutoff w hw
  have hsmall : (1 : ℚ) / (126 * 4 ^ (7 * w.packet.X)) <
      1 / (w.packet.target + 1 : ℕ) := by
    calc
      (1 : ℚ) / (126 * 4 ^ (7 * w.packet.X)) =
          2 * ((1 : ℚ) / (252 * 4 ^ (7 * w.packet.X))) := by
        field_simp
        norm_num
      _ ≤ 2 * w.radius := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ < _ := hg
  have ht : ((w.packet.target + 1 : ℕ) : ℚ) <
      126 * 4 ^ (7 * w.packet.X) :=
    (one_div_lt_one_div (by positivity) (by positivity)).mp hsmall
  exact_mod_cast ht

end GammaAdmission

#print axioms GammaAdmission.binetBeta_lower
#print axioms GammaAdmission.valid_radius_lt_cutoff
#print axioms GammaAdmission.weighted_fold_lower
#print axioms GammaAdmission.arithmetic_radius_lower
#print axioms GammaAdmission.valid_target_bound
