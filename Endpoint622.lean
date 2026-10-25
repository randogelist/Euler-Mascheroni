import Admission622
import GammaAdmission.GeneralEndpoint

/-!
# The admitted target-622 witness attached to the irrationality endpoints

The finite seed is supplied by `Target622.admitted_seed`. Analytic soundness
and the global successor remain explicit mathematical inputs. The adapter
below connects the concrete Binet checker to the existing generic Riesz engine.
-/

namespace GammaAdmission

/-- The concrete Binet contracts supply the generic Riesz engine laws. -/
def binetEngine (bridge : GammaBinetBoundsSound)
    (lock : GammaBinetSuccessor) : RieszEngine gamma where
  Coord := GammaBinetCoord
  check := checkBinet
  next := lock.next
  A := fun w => w.packet.A
  B := fun w => w.packet.B
  upper := fun w => 1 / ((w.packet.target : ℚ) + 1)
  closed := lock.closed
  sound := by
    intro w hw
    obtain ⟨hpos, hsmall⟩ := accepted_binet_sound bridge w hw
    refine ⟨hpos, ?_⟩
    apply le_of_lt
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast,
      GammaCoord.gammaLinear] using hsmall
  decay := by
    intro w hw
    have hlim : Filter.Tendsto
        (fun k : ℕ => (1 : ℝ) / (((k + w.packet.target : ℕ) : ℝ) + 1))
        Filter.atTop (nhds 0) :=
      (Filter.tendsto_add_atTop_iff_nat w.packet.target).2
        tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_add, Rat.cast_natCast,
      lock.target_iter w hw, Nat.add_comm] using hlim

/-- Direct specialization: the admitted seed is no longer a theorem input. -/
theorem GAMMA_TARGET622_DIRECT_ENDPOINT
    (bridge : GammaBinetBoundsSound)
    (lock : GammaBinetSuccessor) :
    Irrational Real.eulerMascheroniConstant :=
  GAMMA_IRRATIONAL_OF_ACCELERATED_ONE_COORDINATE
    bridge lock Target622.admitted_seed

/-- The same concrete seed now activates the generator-independent endpoint. -/
theorem GAMMA_TARGET622_ENDPOINT
    (bridge : GammaBinetBoundsSound)
    (lock : GammaBinetSuccessor) :
    Irrational Real.eulerMascheroniConstant :=
  RieszEngine.one_entry gamma (binetEngine bridge lock)
    Target622.admitted_seed

end GammaAdmission

#check GammaAdmission.binetEngine
#check GammaAdmission.Target622.admitted_seed
#check GammaAdmission.GAMMA_TARGET622_DIRECT_ENDPOINT
#check GammaAdmission.GAMMA_TARGET622_ENDPOINT
#print axioms GammaAdmission.binetEngine
#print axioms GammaAdmission.GAMMA_TARGET622_DIRECT_ENDPOINT
#print axioms GammaAdmission.GAMMA_TARGET622_ENDPOINT
