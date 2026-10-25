# Euler–Mascheroni: finite witness and conditional Lean endpoint

This repository contains the admitted target-622 witness, its formal conditional
irrationality endpoint, and the supporting Lean sources. The endpoint package
passed the owner's native Windows replay under Lean 4.33.0, as recorded in the
supplied terminal transcript. No Lean compilation was performed while preparing
this repository.

The endpoint has two explicit mathematical inputs. **Unconditional irrationality
of the Euler–Mascheroni constant is not proved here.**

## Admitted witness

The raw packet is defined in [GeneratedWitness.lean](GeneratedWitness.lean).

| Field | Value |
|---|---|
| Target | `622` |
| Integer readout | `A = 109110`, `B = 62980` |
| Coefficients | `[-17, -512618, 1461727, -839982]` |
| Binet order | `p = 6` |
| Other coordinates | `X = 4`, `Y = 1`, `j = 1`, `r = 0`, `K = 1`, `R = 4` |

[Admission622.lean](Admission622.lean) proves these closed statements in
`GammaAdmission.Target622`:

```lean
witness_checked : checkBinet witness = true
witness_valid   : witness.Valid
admitted_seed   : ∃ w : GammaBinetCoord, checkBinet w = true
```

Finite validity is an exact arithmetic predicate. Interpreting the enclosure as
a bound on the actual Euler–Mascheroni constant uses `GammaBinetBoundsSound`.

## Formal conditional implication

[Endpoint622.lean](Endpoint622.lean) supplies the admitted witness internally:

```lean
theorem GAMMA_TARGET622_ENDPOINT
    (bridge : GammaBinetBoundsSound)
    (lock : GammaBinetSuccessor) :
    Irrational Real.eulerMascheroniConstant
```

The same file contains the direct endpoint and `binetEngine`, which attaches
the exact Binet checker and witness to the generic Riesz engine. See
[the conditional endpoint contract](docs/CONDITIONAL_ENDPOINT.md) for the
remaining inputs and their precise scope.

| Result | Evidence / status |
|---|---|
| Target-622 finite admission | Owner-reported native Windows PASS |
| Direct and generic endpoint attachment | Owner-reported native Windows PASS |
| Endpoint axiom audit | `propext`, `Classical.choice`, `Quot.sound` |
| Binet soundness | Explicit input; no proof supplied |
| Global Binet successor | Explicit input; no instance supplied |
| Fixed-width target bound | Source and historical compilation receipt included |
| Uniform fixed-order obstruction | On-paper argument; not fully Lean formalized |

The standard axiom audit concerns the conditional theorem; it does not discharge
its parameters. This is a conditional endpoint, not a reduction to finite
checking alone.

## Windows replay

Use the existing Lean **4.33.0** installation and compatible offline Mathlib cache.
From a downloaded or cloned repository folder, run in CMD:

```cmd
call run.cmd
```

The unchanged baseline runner compiles twelve modules in a fresh `results` work
directory. It does not download dependencies. Its historical package identifier
is intentionally retained. The default paths are:

```text
%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe
%USERPROFILE%\lean-native\awpi_phi_rh_lean_sieved_v0_1_1
```

Override them with `GAMMA_LEAN_EXE` and `GAMMA_CACHE_ROOT`, or supply the complete
dependency path with `GAMMA_LEAN_PATH`. The packages do not record a Mathlib
commit; a portable, pinned Lake environment is not provided. Mathlib and compiled
`.olean` files are not vendored.

Successful endpoint replay ends with:

```text
LEAN_REPLAY=PASS
FINITE_ADMISSION=PASS
CONDITIONAL_ENDPOINT=PASS
GENERIC_ENGINE_ATTACHMENT=PASS
BINET_SOUNDNESS=EXPLICIT_INPUT
BINET_SUCCESSOR=EXPLICIT_INPUT
UNCONDITIONAL_GAMMA_IRRATIONALITY=NOT_PROVED
```

## Fixed-order audit

[Closure622.lean](Closure622.lean) contains `valid_target_bound`:

```lean
w.Valid → w.packet.target + 1 < 126 * 4 ^ (7 * w.packet.X)
```

This is a width-dependent bound. The further uniform bound
`target + 1 < 126 * 4^77` and the resulting no-successor argument are preserved
in [MATHEMATICAL_OBSTRUCTION.txt](docs/MATHEMATICAL_OBSTRUCTION.txt), explicitly
marked as not yet Lean formalized. Choosing width 11 does not supply a global
successor. The audit is about this fixed-order checker, not gamma's rationality.

For an owner-run replay that also includes `Closure622.lean`, use:

```cmd
call audit-fixed-order.cmd
```

## Provenance

All thirteen Lean source files and both CMD runners were copied unchanged from
the recovered endpoint and fixed-order audit packages. Historical receipts are
under [verification/historical](verification/historical); their old
`USER_RUN_PENDING` endpoint status is superseded by the owner's supplied Windows
PASS transcript. The fixed-order receipt has one local path redacted.

[publication_provenance.json](verification/publication_provenance.json) records
the source archive hashes and evidence scope.
[SHA256SUMS.txt](SHA256SUMS.txt) records the repository snapshot's file hashes.
