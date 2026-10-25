# Conditional endpoint contract

The seed obligation is discharged by
`GammaAdmission.Target622.admitted_seed`. Both named irrationality endpoints
consume that theorem internally.

The remaining inputs are defined in
[`GammaAdmission/AcceleratedAdmission.lean`](../GammaAdmission/AcceleratedAdmission.lean):

```lean
structure GammaBinetBoundsSound : Prop where
  enclosure : ∀ w : GammaBinetCoord, w.arithmeticReady →
    (w.lower : ℝ) ≤ w.packet.gammaLinear ∧
    w.packet.gammaLinear ≤ (w.upper : ℝ)

structure GammaBinetSuccessor where
  next : GammaBinetCoord → GammaBinetCoord
  closed : ∀ w : GammaBinetCoord, checkBinet w = true →
    checkBinet (next w) = true
  target_step : ∀ w : GammaBinetCoord, checkBinet w = true →
    (next w).packet.target = w.packet.target + 1
```

Thus the first input concerns every arithmetically ready packet, and the second
requires universal preservation and target growth. Neither is a field of the
finite raw witness or a result established by its successful check.

The verified conditional chain is:

1. The concrete finite witness passes `checkBinet`.
2. A supplied successor preserves acceptance along its iterates and increments
   the target.
3. Supplied Binet soundness turns every accepted packet into a nonzero integer
   linear form with absolute value below `1 / (target + 1)`.
4. Those bounds tend to zero; `irrational_of_qiw` or `RieszEngine.one_entry`
   yields `Irrational Real.eulerMascheroniConstant`.

In the generic adapter, soundness and decay are derived from the two supplied
inputs. Packaging those laws inside a structure does not construct their inputs.

For the specific seed, the actual gamma inequality

\[
0 < |109110\gamma - 62980| < 1/623
\]

is a consequence conditional on Binet soundness. Finite checker acceptance and
the integer readout are closed theorems independent of that assumption.

The fixed-order checker restricts `p ≤ 6`. Its archived obstruction argument
must be considered before trying to instantiate the successor. The repository
contains a Lean width-dependent bound and an additional on-paper uniform bound;
it contains no Lean theorem establishing the uniform bound or constructing the
successor.

In the project's workflow terminology, this endpoint does not meet the
finite-checker-only `FORMAL_CLOSURE` gate: two global inputs remain after seed
admission. No unconditional irrationality or S-Tier claim is made.
