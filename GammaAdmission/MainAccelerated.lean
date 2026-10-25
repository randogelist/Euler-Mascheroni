import GammaAdmission.AcceleratedAdmission
import GammaAdmission.SamplesAccelerated

/-!
One entrypoint for the accelerated Binet and original dyadic packets.
`#print axioms` checks what the kernel declarations depend on; the endpoint
has GammaBinetBoundsSound and GammaBinetSuccessor as EXPLICIT hypotheses.
-/

#print axioms GammaAdmission.checkBinet_iff
#print axioms GammaAdmission.accepted_binet_sound
#print axioms GammaAdmission.GAMMA_IRRATIONAL_OF_ACCELERATED_ONE_COORDINATE
