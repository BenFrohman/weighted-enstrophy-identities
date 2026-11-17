# Kernel certificate: weighted-enstrophy-identities

This file records a reproducible machine check of the Lean 4 development in this repository. Lean does not issue a signed "official" certificate. What is recorded here is the exact commit and toolchain, the complete `lake build` log, a scan for `sorry`/`admit`/`native_decide`/`axiom`, the `#print axioms` result for every theorem the build produces, and a replay of every module through Lean's kernel with the toolchain's `leanchecker`. Each check can be rerun with the command at the end.

| Item | Value |
|---|---|
| Repository | https://github.com/BenFrohman/weighted-enstrophy-identities |
| Certified commit | `d573271942483ddb756063829a839eb55a6b0e99` (branch `fix/textbook-notation-20261116`) |
| Lean sources | `.lean`, lakefile, manifest and toolchain files exactly as at the certified commit; the commit that adds this certificate changes only files under `certificates/` |
| lake | Lake version 5.0.0-src+714601b (Lean version 4.30.0-rc1) |
| elan | installed in CI by `elan-init.sh` from leanprover/elan (master), toolchain taken from `lean-toolchain`; the workflow does not print the elan version |
| lake-manifest.json sha256 | `c555d6ea977bf91b2e18686450cdd4d22cb5936fa63e782319b27f152c2b0560` |
| lean-toolchain | `leanprover/lean4:v4.30.0-rc1` |
| Lean | Lean (version 4.30.0-rc1, x86_64-unknown-linux-gnu, commit 714601baf118066cbf3f282361339c6d06665b2a, Release) |
| Mathlib | `0c154d67103f74be3a0f2c509f72ccbf5be9f2a7` (lake-manifest.json; inputRev `v4.30.0-rc1`) |
| Date (UTC) | 2026-11-17T06:50:03Z |
| CI run | https://github.com/BenFrohman/weighted-enstrophy-identities/actions/runs/44034090289 |
| `lake build` | `Build completed successfully (8272 jobs).` ([build.log](build.log)) |
| sorry / admit / native_decide / axiom scan | `RESULT: 0 hits` ([sorry-scan.txt](sorry-scan.txt)) |
| `#print axioms` | `AUDIT PASS: 101 theorems in 7 modules depend only on propext, Classical.choice, Quot.sound (or on no axioms)` ([axioms.txt](axioms.txt)) |
| Kernel replay (leanchecker) | `RESULT: 8 of 8 modules replayed through the kernel, 0 failures` ([leanchecker.txt](leanchecker.txt)) |

## What each check means

- **Build.** `lake build` of the default targets with the pinned toolchain. Mathlib comes from `lake exe cache get` (it is never rebuilt from source). The build elaborates every proof and sends each declaration to Lean's kernel.
- **Scan.** `certificates/tools/sorry_scan.py` strips comments and strings from every tracked `.lean` file and reports any `sorry`, `admit`, `native_decide` or `axiom` declaration. Result: RESULT: 0 hits.
- **Axioms.** `certificates/tools/gen_audit.py` imports all 8 built modules ([modules.txt](modules.txt)) and calls `Lean.collectAxioms`, the function behind `#print axioms`, on every theorem declared in them (101 theorems, auto-generated internal names excluded). `check_audit.py` fails unless each depends only on `propext`, `Classical.choice` and `Quot.sound`, or on no axioms. Raw output: [axioms.raw.txt](axioms.raw.txt); generated Lean file: [KernelCertificateAudit.lean.txt](KernelCertificateAudit.lean.txt).
- **Kernel replay.** checker: leanchecker source shipped with v4.30.0-rc1 (src/lean/LeanChecker.lean), prefix match -> exact match, run with lean --run. For each module, the checker loads the module's imports from their `.olean` files and replays every declaration of that module through the kernel. The stock checker treats its argument as a module-name prefix and replays all matching modules in parallel, which runs out of memory on a root module, so it is run once per module with exact matching (the one-line patch is printed in [leanchecker.txt](leanchecker.txt)). The checker's own documentation describes it as a tool to detect environment hacking, not an independent external verifier; imported Mathlib and core declarations are trusted from their `.olean` files.

## Scope

The axiom result says the listed theorems are proved from Lean's standard axioms. It does not by itself say what the theorems mean; read the statements in the sources. Conditional theorems remain conditional on their hypotheses.

## Rebuild

```
git clone https://github.com/BenFrohman/weighted-enstrophy-identities.git && cd weighted-enstrophy-identities && git checkout d573271942483ddb756063829a839eb55a6b0e99 && lake exe cache get && lake build && python3 certificates/tools/sorry_scan.py && python3 certificates/tools/gen_audit.py /tmp/KernelCertificateAudit.lean /tmp/modules.txt && lake env lean /tmp/KernelCertificateAudit.lean > /tmp/axioms.raw.txt && python3 certificates/tools/check_audit.py /tmp/axioms.raw.txt | tail -n 1
```
