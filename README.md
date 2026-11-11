# weighted-enstrophy-identities

[![certify.yml](https://github.com/BenFrohman/weighted-enstrophy-identities/actions/workflows/certify.yml/badge.svg?branch=main)](https://github.com/BenFrohman/weighted-enstrophy-identities/actions/workflows/certify.yml)

Lean 4 + Mathlib (`leanprover/lean4:v4.30.0-rc1`, Mathlib `v4.30.0-rc1`) formalization of two
exact balance identities, and related lemmas, for the 3-D incompressible Navier–Stokes vorticity equation on the
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
   `K`-algebra `A` with three spatial derivations `∂ₖ`, a time derivation `∂ₜ`, a `K`-linear
   integral `I : A → B` and a map `Dₜ : B → B` with `I(∂ₖf) = 0` and `I(∂ₜf) = Dₜ(I f)`.
   Both identities follow from these two properties alone.
2. **Trigonometric polynomials on `T³`** (`WeightedEnstrophy/TrigModel.lean`): finite sums
   `Σₙ fₙ e^{2πi n·x}`, coefficients in any commutative `ℂ`-algebra `R` with a derivation `D`
   (`enstrophy_identity_T3`, `weighted_identity_T3`).
3. **Smooth periodic fields** (`WeightedEnstrophy/Smooth.lean`): `A` is the algebra of real
   `C^∞` functions `f(t,a,b,c)` on `ℝ × ℝ³` that are 1-periodic in each of `a, b, c`, i.e.
   smooth time-dependent fields on `T³ = (ℝ/ℤ)³`. Here `∂ₖ, ∂ₜ` are Fréchet partial derivatives,
   `I f (t) = ∫₀¹∫₀¹∫₀¹ f(t,a,b,c) dc db da` and `Dₜ = d/dt`. Both properties of `I` are proved:
   - `Smooth.int_d`: `∫_{T³} ∂ₖ f = 0` (from `Torus.torusIntegral_deriv_a/b/c`, which hold for
     `C¹` integrands periodic in the differentiated variable);
   - `Smooth.hasDerivAt_I`, `Smooth.int_dt`: `d/dt ∫_{T³} f = ∫_{T³} ∂ₜ f` (from
     `Torus.hasDerivAt_torusIntegral`, which holds when `f` and `∂ₜf` are jointly continuous).

   So `Smooth.enstrophy_identity_smooth` and `Smooth.weighted_identity_smooth` hold for every
   smooth periodic `u, ω, φ` satisfying `div u = 0`, the vorticity equation and the weight
   equation, which enter as hypotheses.

## Further results (`WeightedEnstrophy/Lyapunov.lean`, `WeightedEnstrophy/Fourier/`)

Proved:
- `Fourier.L2_strain_eq`: for `L²(T³)` fields whose Fourier coefficients are those of a
  divergence-free `u`, its vorticity and its strain `S = ½(∇u+∇uᵀ)`,
  `Σᵢⱼ‖Sᵢⱼ‖₂² = ½ Σᵢ‖ωᵢ‖₂²`. `Fourier.L2_strain_le` gives `‖S‖₂ ≤ ‖ω‖₂`.
- `Lyapunov.dS_identity_smooth`: for `S = ½∫|ω|² − (κ/2)∫|ω|⁴φ` and smooth periodic solutions,
  `S' = ∫ωᵢωⱼ∂ⱼuᵢ − ν∫|∇ω|² − (κ/2)(4∫|ω|²φ ωᵢωⱼ∂ⱼuᵢ + 4ν∫|ω|²φ ω·Δω + ∫|ω|⁶)`. This is an
  exact identity. It contains no sup-norm `M(t)`.
- `Lyapunov.le_integral_sq_of_deriv`: if `g(0)=0` and `g' = h ≤ M²` on `[0,t]` (`h, M`
  continuous), then `g(t) ≤ ∫₀ᵗ M²`. Applied to `g(s) = φ(s,X(s))` along a particle path, this is
  the bound `φ ≤ ∫₀ᵗ M²`. The chain rule along the path is not formalized.
- `Lyapunov.ode_bounded`: when `κ > 0`, every solution of `y' = y²(C − κy)` on `[0,T]` satisfies
  `min(y₀, C/κ, 0) ≤ y(t) ≤ max(y₀, C/κ, 0)`. This needs no assumption on `T`.

Stated as `Prop` definitions. They are not proved, and no theorem above uses them:
- `CalderonZygmundLp p`: `∫|∂ⱼuᵢ|^p ≤ C∫|ω|^p` on smooth periodic divergence-free fields. This
  is the classical theorem for `1 < p < ∞`, and it is not formalized here. The `L∞` version is
  false and is not stated.
- `WeightedToSupReduction κ ν`: a bound on `S` over `[0,T)` would force a bound on `sup|ω|²` over the same `[0,T)`, with a constant that may depend on `T`.
- `PhiSupControl ν`: for each horizon `T`, a bound on `|φ|` over `[0,T)`; the bound may depend on `T`.

The repository contains no regularity theorem for Navier–Stokes. The absorption step that uses
an `L∞` Calderón–Zygmund bound, the reduction from `S` to `M`, and the bootstrap are not proved.

## Layout

- `WeightedEnstrophy/Abstract.lean`, `TrigModel.lean`, `TorusCalculus.lean`, `Smooth.lean`,
  `Lyapunov.lean`, `Fourier/Basic.lean`, `Fourier/Strain.lean`
- `AxiomAudit.lean`: kernel axiom audit
- `paper/main.tex`: step-by-step derivations
- `ip_pipeline/seal_and_verify.py`, `audit/`, `PROVENANCE_MERKLE_ROOT.json`: Titan-Audit,
  SealGuard and Sentinel-Gate certificates over git-tracked files

License: Apache-2.0. © 2026 Benjamin Stanley Frohman (ORCID 0009-0006-7068-3718).

## Copyright, license and scope

Copyright 2026 Benjamin Stanley Frohman (ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)). Licensed under the Apache License, Version 2.0; see `LICENSE` and `NOTICE`.

What is proved vs. conditional: The balance identities are proved for the class stated in "On what class these are proved"; any remaining assumptions are named `Prop`s passed explicitly. Every hypothesis is a named `Prop` passed as an explicit argument. Nothing in this repository claims to solve the Clay Millennium problem or global regularity for unmodified 3D Navier–Stokes.

## Citation

Cite this work with [`CITATION.cff`](CITATION.cff) (GitHub's "Cite this repository" button).
