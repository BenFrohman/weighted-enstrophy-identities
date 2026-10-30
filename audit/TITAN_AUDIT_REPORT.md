# titan-audit report: `weighted-enstrophy-identities`

**Verdict: PASS**

- Generated (UTC): 2026-10-30T17:38:15+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `2efffa814145df03a7baac9d0077b06d444d3d91`
- Tree SHA-256: `410df46bb674f56d8bc9c540adefa64f14a5c77c23d4d853b6a65db6d9c9ea39` over 12 files

## Build

- Build skipped (`--no-build`); audit used existing .olean files.

## Axiom audit

- Modules: 8  Theorems: 101  Clean (only propext/Classical.choice/Quot.sound): 101
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|
| `WeightedEnstrophy.Abstract` | 24 | 0 |
| `WeightedEnstrophy.Fourier.Basic` | 11 | 0 |
| `WeightedEnstrophy.Fourier.Strain` | 17 | 0 |
| `WeightedEnstrophy.Lyapunov` | 5 | 0 |
| `WeightedEnstrophy.Smooth` | 14 | 0 |
| `WeightedEnstrophy.TorusCalculus` | 16 | 0 |
| `WeightedEnstrophy.TrigModel` | 14 | 0 |

## Source scan

Counts: none


### Vacuity heuristics (in build)

- none

Heuristics are advisory: a flag means *look here*, not *wrong*.

## Signature

- ed25519 public key (base64): `ZOyujV1yUEldQRZEDhmXCHa4ikWGfcTD+meZYssNLpo=`
- Verify: `titan-audit verify report.json`
