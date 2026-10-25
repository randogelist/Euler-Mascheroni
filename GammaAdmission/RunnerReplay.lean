import GammaAdmission.SamplesAccelerated

/-!
# Kernel replay of the known Gamma seed

This file replaces a displayed Boolean evaluation with a named theorem.
It proves only finite arithmetic unconditionally. The analytic enclosure and
the globally closed successor remain explicit arguments of every conclusion
about native gamma. No native evaluation tactic is used for proofs.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

namespace GammaAdmission

macro "gamma_packet_arithmetic" : tactic =>
  `(tactic| norm_num [checkBinet, GammaBinetCoord.arithmeticCheck,
    GammaCoord.arithmeticCheck, GammaBinetCoord.intervalCheck,
    GammaBinetCoord.cancellationCheck, GammaCoord.A,
    GammaCoord.derivAtOne, GammaCoord.readoutQ, harmonicQ,
    GammaBinetCoord.lower, GammaBinetCoord.upper,
    GammaBinetCoord.center, GammaBinetCoord.radius,
    GammaCoord.polyEval, binetBeta, binetSign,
    Finset.sum_Icc_succ_top, Finset.sum_range_succ])

/-- The baseline finite packet passes the exact checker, by kernel reduction. -/
theorem fastGammaGood_checked : checkBinet fastGammaGood = true := by
  unfold fastGammaGood
  gamma_packet_arithmetic

/-- The checker reflection theorem gives the finite admission proposition. -/
theorem fastGammaGood_valid : fastGammaGood.Valid :=
  (checkBinet_iff fastGammaGood).mp fastGammaGood_checked

/-- A rejected integer readout is also checked by kernel reduction. -/
theorem fastGammaBadB_rejected : checkBinet fastGammaBadB = false := by
  unfold fastGammaBadB fastGammaGood
  gamma_packet_arithmetic

/-- The known packet does not meet the stronger requested target. -/
theorem fastGammaBadTarget_rejected :
    checkBinet fastGammaBadTarget = false := by
  unfold fastGammaBadTarget fastGammaGood
  gamma_packet_arithmetic

/-- Native-gamma soundness remains conditional on the analytic bridge. -/
theorem runner_seed_sound (bridge : GammaBinetBoundsSound) :
    0 < |fastGammaGood.packet.gammaLinear| ∧
      |fastGammaGood.packet.gammaLinear| <
        1 / ((fastGammaGood.packet.target : ℝ) + 1) :=
  accepted_binet_sound bridge fastGammaGood fastGammaGood_checked

/-- The finite seed is discharged. Both global mathematical inputs remain. -/
theorem GAMMA_IRRATIONAL_OF_PROVED_BRIDGE_AND_PROVED_SUCCESSOR
    (bridge : GammaBinetBoundsSound)
    (E : GammaBinetSuccessor) :
    Irrational Real.eulerMascheroniConstant :=
  GAMMA_IRRATIONAL_OF_ACCELERATED_ONE_COORDINATE
    bridge E ⟨fastGammaGood, fastGammaGood_checked⟩

end GammaAdmission

#print axioms GammaAdmission.fastGammaGood_checked
#print axioms GammaAdmission.fastGammaGood_valid
#print axioms GammaAdmission.fastGammaBadB_rejected
#print axioms GammaAdmission.fastGammaBadTarget_rejected
#print axioms GammaAdmission.runner_seed_sound
#print axioms GammaAdmission.GAMMA_IRRATIONAL_OF_PROVED_BRIDGE_AND_PROVED_SUCCESSOR
