import GeneratedWitness

/-!
Finite admission of the explicit target-622 packet.
These theorems have no analytic-bridge or global-successor hypotheses.
The imported witness retains separate, explicitly conditional consequences.
-/

namespace GammaAdmission.Target622

abbrev witness : GammaBinetCoord := RunnerCandidate.witness

theorem witness_checked : checkBinet witness = true :=
  RunnerCandidate.witness_checked

theorem witness_valid : witness.Valid :=
  (checkBinet_iff witness).mp witness_checked

theorem witness_data :
    witness.packet.target = 622 ∧
    witness.packet.A = 109110 ∧
    witness.packet.B = 62980 ∧
    witness.p = 6 ∧
    witness.packet.coeff = [-17, -512618, 1461727, -839982] := by
  norm_num [witness, RunnerCandidate.witness, GammaCoord.A]

/-- The finite existential input of the existing endpoint is discharged. -/
theorem admitted_seed : ∃ w : GammaBinetCoord, checkBinet w = true :=
  ⟨witness, witness_checked⟩

/-- Closed finite admission with the explicit target and integer readout. -/
theorem GAMMA_TARGET622_FINITE_ADMISSION :
    ∃ w : GammaBinetCoord,
      w.Valid ∧ w.packet.target = 622 ∧
      w.packet.A = 109110 ∧ w.packet.B = 62980 :=
  ⟨witness, witness_valid, witness_data.1,
    witness_data.2.1, witness_data.2.2.1⟩

end GammaAdmission.Target622

#check GammaAdmission.Target622.witness_checked
#check GammaAdmission.Target622.witness_valid
#check GammaAdmission.Target622.witness_data
#check GammaAdmission.Target622.admitted_seed
#check GammaAdmission.Target622.GAMMA_TARGET622_FINITE_ADMISSION
#print axioms GammaAdmission.Target622.witness_checked
#print axioms GammaAdmission.Target622.witness_valid
#print axioms GammaAdmission.Target622.witness_data
#print axioms GammaAdmission.Target622.admitted_seed
#print axioms GammaAdmission.Target622.GAMMA_TARGET622_FINITE_ADMISSION
