# titan-audit report: `weighted-enstrophy-identities`

**Verdict: PASS**

- Generated (UTC): 2026-10-30T17:14:45+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `c29682ef315586cae2b35b901d92fd209613d95b`
- Tree SHA-256: `3c1b2466a5068d7bb3ae58b06faff7e1d098a45401ee758d2badb71c9917477c` over 7 files

## Build

- Build skipped (`--no-build`); audit used existing .olean files.

## Axiom audit

- Modules: 3  Theorems: 38  Clean (only propext/Classical.choice/Quot.sound): 38
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|
| `WeightedEnstrophy.Abstract` | 24 | 0 |
| `WeightedEnstrophy.TrigModel` | 14 | 0 |

## Source scan

Counts: none


### Vacuity heuristics (in build)

- none

Heuristics are advisory: a flag means *look here*, not *wrong*.

## Signature

- ed25519 public key (base64): `ZOyujV1yUEldQRZEDhmXCHa4ikWGfcTD+meZYssNLpo=`
- Verify: `titan-audit verify report.json`
