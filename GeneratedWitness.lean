import GammaAdmission.RunnerReplay

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

namespace GammaAdmission.RunnerCandidate

def witness : GammaBinetCoord :=
  { packet :=
      { X := 4, Y := 1, j := 1, r := 0, K := 1, R := 4,
        target := 622, coeff := [-17, -512618, 1461727, -839982], B := 62980 },
    p := 6 }

theorem witness_checked : checkBinet witness = true := by
  unfold witness
  gamma_packet_arithmetic

theorem witness_valid : witness.Valid := (checkBinet_iff witness).mp witness_checked

theorem witness_sound (bridge : GammaBinetBoundsSound) :
  0 < |witness.packet.gammaLinear| ∧
  |witness.packet.gammaLinear| < 1 / ((witness.packet.target : ℝ) + 1) :=
  accepted_binet_sound bridge witness witness_checked

theorem irrational_if_bridge_and_lock (bridge : GammaBinetBoundsSound)
    (lock : GammaBinetSuccessor) : Irrational Real.eulerMascheroniConstant :=
  GAMMA_IRRATIONAL_OF_ACCELERATED_ONE_COORDINATE bridge lock ⟨witness, witness_checked⟩

end GammaAdmission.RunnerCandidate

#print axioms GammaAdmission.RunnerCandidate.witness_checked
#check GammaAdmission.RunnerCandidate.witness_sound
#check GammaAdmission.RunnerCandidate.irrational_if_bridge_and_lock
#print axioms GammaAdmission.RunnerCandidate.irrational_if_bridge_and_lock
