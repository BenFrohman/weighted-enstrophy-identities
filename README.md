# weighted-enstrophy-identities

Lean 4 + Mathlib (`leanprover/lean4:v4.30.0-rc1`, Mathlib `v4.30.0-rc1`) formalization of two
exact balance identities for the 3-D incompressible Navier–Stokes vorticity equation on the
torus `T³`, from *An a-posteriori Lyapunov functional approach* by Benjamin Stanley Frohman.
Build: `lake build`, 0 `sorry`; `lake env lean AxiomAudit.lean` reports only `propext`,
`Classical.choice`, `Quot.sound`.

## Setting

Fields `u, ω : T³ → ℝ³` (time-dependent), scalar weight `φ`, with
`div u = 0`, the vorticity equation `∂ₜω + (u·∇)ω = (ω·∇)u + νΔω`, and the weight equation
`∂ₜφ + u·∇φ = |ω|²`. The relation `ω = curl u` is not used by either identity.

## Theorems

**Identity (1)** (`WeightedEnstrophy.enstrophy_identity`, `Trig.enstrophy_identity_T3`).
For `E = ½∫|ω|²` and `P = ∫ ωᵢωⱼ∂ⱼuᵢ`:
`dE/dt = P − ν∫|∇ω|²`
(formalized as `d/dt ∫|ω|² = 2P − 2ν∫|∇ω|²`). The transport term is
`Σₖ∂ₖ(uₖ|ω|²/2) − (div u)|ω|²/2` and integrates to zero.

**Identity (2)** (`WeightedEnstrophy.weighted_identity`, `Trig.weighted_identity_T3`).
For `Q = ∫|ω|⁴φ`:
`dQ/dt = 4∫|ω|²φ ω·(ω·∇)u + 4ν∫|ω|²φ ω·Δω + ∫|ω|⁶`.
The two transport terms combine into `(u·∇)(|ω|⁴φ) = Σₖ∂ₖ(uₖ|ω|⁴φ) − (div u)|ω|⁴φ`, which
integrates to zero. `stretch_eq` identifies `Σᵢⱼ ωᵢωⱼ∂ⱼuᵢ` with `ω·(ω·∇)u`.

Supporting results: the torus divergence lemma `int_adv_eq_zero` (`∫(u·∇)g = 0` when
`div u = 0`), the pointwise identities `adv_eq`, `wLapW_eq` (`ω·Δω = Σₖ∂ₖ(ωᵢ∂ₖωᵢ) − |∇ω|²`),
`two_w_adv`, and the pre-integration forms `dt_vsq_div`, `dt_weighted_div`.

## On what class these are proved

1. **Any periodic differential algebra** (`WeightedEnstrophy/Abstract.lean`): a commutative
   `K`-algebra `A` of fields with three spatial derivations `∂ₖ`, a time derivation `∂ₜ`,
   and a `K`-linear integral `I` with `I(∂ₖf) = 0` and `I(∂ₜf) = Dₜ(I f)`. Both identities are
   proved from these two properties of `I` alone.
2. **Trigonometric polynomials on `T³`** (`WeightedEnstrophy/TrigModel.lean`): fields
   `Σₙ fₙ e^{2πi n·x}` (finite sums, `n ∈ ℤ³`) with coefficients in any commutative
   `ℂ`-algebra `R` with a derivation `D` acting as `d/dt` on coefficients. Here `∂ₖ` is
   multiplication of mode `n` by `2πi nₖ`, `∫_{T³}` is the zero-mode coefficient, and the two
   properties of `I` are proved (`integral_dx`, `integral_dt`), so identities (1) and (2)
   hold unconditionally on this class.

General smooth periodic fields are not instantiated: that requires differentiation under
the integral sign and the divergence theorem for smooth functions on `T³`, which are not
formalized here.

The repository contains only these identities. It makes no regularity statement about
Navier–Stokes solutions.

## Layout

- `WeightedEnstrophy/Abstract.lean`, `WeightedEnstrophy/TrigModel.lean`
- `AxiomAudit.lean`: kernel axiom audit
- `paper/main.tex`: step-by-step derivations
- `ip_pipeline/seal_and_verify.py`, `audit/`, `PROVENANCE_MERKLE_ROOT.json`: Titan-Audit,
  SealGuard and Sentinel-Gate certificates over git-tracked files

License: Apache-2.0. © 2026 Benjamin Stanley Frohman (ORCID 0009-0006-7068-3718).
