import GammaAdmission.AcceleratedAdmission

/-!
# Accelerated rational admission samples
No irrationality theorem is derived from these finite computations.
The analytic Binet enclosure theorem and infinite successor are open.
-/

namespace GammaAdmission

/-- Self-contained p=2 accelerated packet; target 6 gives threshold 1/7. -/
def fastGammaGood : GammaBinetCoord :=
  { packet :=
      { X := 3, Y := 1, j := 1, r := 0,
        K := 4, R := 10, target := 6,
        coeff := [-180, 510, -280], B := 29 },
    p := 2 }

def fastGammaBadB : GammaBinetCoord :=
  { fastGammaGood with packet := { fastGammaGood.packet with B := 30 } }

def fastGammaBadTarget : GammaBinetCoord :=
  { fastGammaGood with packet := { fastGammaGood.packet with target := 100 } }

-- Expected finite checks: true, false, false.
#eval checkBinet fastGammaGood
#eval checkBinet fastGammaBadB
#eval checkBinet fastGammaBadTarget

#eval fastGammaGood.center
#eval fastGammaGood.radius
#eval fastGammaGood.lower
#eval fastGammaGood.upper

end GammaAdmission
