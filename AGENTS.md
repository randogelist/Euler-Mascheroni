# Repository working rules

- Do not compile Lean locally in automated editing sessions. The owner performs
  native Windows verification, unless a different verification route is
  explicitly authorized.
- Preserve the target-622 witness and exact theorem hypotheses. Do not describe
  finite admission or a conditional endpoint as unconditional irrationality.
- Keep historical verification evidence separate from new runs. Source review,
  hash comparison and import checks are not Lean compilation.
- The existing CMD scripts use an installed Lean 4.33.0 and compatible Mathlib
  cache. Do not silently introduce dependency downloads or a new toolchain.
- Do not commit generated build files, local caches or private machine paths.
- Record source changes that invalidate prior proof verification; do not claim
  reuse without matching source and environment evidence.
