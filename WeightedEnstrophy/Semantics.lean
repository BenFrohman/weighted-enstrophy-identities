/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import WeightedEnstrophy.Smooth

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/main.tex
PAPER_SECTION: The smooth-model theorem of Section "Smooth periodic fields" (`Smooth.enstrophy_identity_smooth`, `Smooth.weighted_identity_smooth`): identities (1) AND (2) for all u, ω, φ ∈ A satisfying (div)–(wt); Theorems "Identity (1)" and "Identity (2)"; Setting equations (div), (vort), (wt)
PAPER_SHA256: c23af493e94fb06598dc46b354bd692b977352aebcfd344bd701a2acaa0cd754

Locked paper claim, quoted verbatim (identity (1), identity (2), the smooth-model theorem that
states both, then the paper's definitions it uses):

PAPER_QUOTE_BEGIN
\begin{theorem}[Identity (1), \texttt{enstrophy\_identity}, \texttt{enstrophy\_identity\_T3}]
With $E=\frac12\int|\omega|^2$ and $P=\int\omega_i\omega_j\partial_ju_i$,
\[\frac{dE}{dt}=P-\nu\int_{\mathbb{T}^3}|\nabla\omega|^2 .\]
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{theorem}[Identity (2), \texttt{weighted\_identity}, \texttt{weighted\_identity\_T3}]
With $Q=\int|\omega|^4\phi$,
\[\frac{dQ}{dt}=4\int|\omega|^2\phi\,\omega\cdot(\omega\cdot\nabla)u+4\nu\int|\omega|^2\phi\,\omega\cdot\Delta\omega+\int|\omega|^6 .\]
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{theorem}[\texttt{Smooth.int\_d}, \texttt{Smooth.int\_dt}, \texttt{Smooth.enstrophy\_identity\_smooth}, \texttt{Smooth.weighted\_identity\_smooth}]
The smooth model is a periodic setting. Hence identities (1) and (2) hold for all
$u,\omega,\phi\in A$ satisfying (\ref{div})--(\ref{wt}).
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
Let $u,\omega:\mathbb{T}^3\to\mathbb{R}^3$ and $\phi:\mathbb{T}^3\to\mathbb{R}$ depend on $t$, with
\begin{align}
&\partial_k u_k=0, \label{div}\\
&\partial_t\omega_i=-u_k\partial_k\omega_i+\omega_k\partial_k u_i+\nu\,\partial_k\partial_k\omega_i,\label{vort}\\
&\partial_t\phi=-u_k\partial_k\phi+|\omega|^2,\label{wt}
\end{align}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
summing over repeated indices. The relation $\omega=\nabla\times u$ is not needed for either identity.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
$A$ is the algebra of $f\in C^\infty(\mathbb{R}\times\mathbb{R}^3,\mathbb{R})$, $f=f(t,a,b,c)$, with
$f(p+e_k)=f(p)$ for the unit spatial vectors $e_1,e_2,e_3$. $\partial_k f(p)=Df(p)e_k$,
$\partial_tf(p)=Df(p)e_t$, $I(f)(t)=\int_0^1\!\int_0^1\!\int_0^1 f(t,a,b,c)\,dc\,db\,da$, $D_t=\frac{d}{dt}$.
PAPER_QUOTE_END

Reading of the paper's terms (all from the quoted text):
* fields are `f : ℝ × ℝ³ → ℝ`, `f = f(t,a,b,c)`, of class `C^∞` and 1-periodic in each spatial
  unit vector `e₁, e₂, e₃` (`paperE`);
* `∂ₖ f(p) = Df(p) eₖ` and `∂ₜ f(p) = Df(p) e_t` with `e_t = (1,0,0,0)` (Fréchet derivative `fderiv`);
* `∫_{T³} f` at time `t` is `∫₀¹∫₀¹∫₀¹ f(t,a,b,c) dc db da` (`paperInt`), `d/dt` is `deriv`;
* `|ω|² = Σᵢ ωᵢ²`, `|∇ω|² = Σᵢ Σₖ (∂ₖωᵢ)²`, `P = ∫ ωᵢωⱼ∂ⱼuᵢ`, summing over repeated indices;
* `|ω|⁴ = (Σᵢ ωᵢ²)²`, `|ω|⁶ = (Σᵢ ωᵢ²)³`, `ω·(ω·∇)u = Σᵢ ωᵢ Σⱼ ωⱼ ∂ⱼuᵢ`,
  `ω·Δω = Σᵢ ωᵢ Σₖ ∂ₖ∂ₖωᵢ`, `Q = ∫|ω|⁴φ`;
* hypotheses (all three, as the smooth-model theorem says "satisfying (div)–(wt)"): (div)
  `∂ₖuₖ = 0`, (vort) `∂ₜωᵢ = -uₖ∂ₖωᵢ + ωₖ∂ₖuᵢ + ν∂ₖ∂ₖωᵢ`, (wt) `∂ₜφ = -uₖ∂ₖφ + |ω|²`, pointwise,
  with `u, ω, φ ∈ A`;
* the conclusion is BOTH displayed identities at every `t`: (1) `dE/dt = P - ν∫|∇ω|²` with
  `E = ½∫|ω|²`, and (2) `dQ/dt = 4∫|ω|²φ ω·(ω·∇)u + 4ν∫|ω|²φ ω·Δω + ∫|ω|⁶`.

`formal_claim` is the conjunction of the statements of `WeightedEnstrophy.Smooth.enstrophy_identity_smooth`
and `WeightedEnstrophy.Smooth.weighted_identity_smooth`, under the common hypotheses (div), (vort),
(wt), phrased in the repository's subalgebra `Smooth.A` with `div`, `VorticityEq`, `WeightEq`, `vsq`,
`stretch`, `gradSq`, `wLapW` and the factor-2 form `D_t I(|ω|²) = 2 I(…) - 2ν I(…)`. `paper_claim` uses plain functions, `fderiv` and
iterated interval integrals. The correspondence packages functions into `Smooth.A` and back and
converts the factor-2 form into the paper's `E = ½∫|ω|²` form.

Scope: two exact identities for smooth periodic solutions of (div), (vort), (wt). It gives no bound
and makes no regularity claim; the Clay Millennium problem remains open.
-/

namespace TruthGate

open scoped ContDiff
open WeightedEnstrophy WeightedEnstrophy.Smooth

-- TRUTH-GATE LOCK BEGIN
/-- The paper's spatial unit vectors `e₁, e₂, e₃` in `ℝ × ℝ³` (coordinates `(t, a, b, c)`). -/
def paperE : Fin 3 → ℝ × ℝ × ℝ × ℝ := ![(0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1)]

/-- The paper's `I(f)(t) = ∫₀¹∫₀¹∫₀¹ f(t,a,b,c) dc db da`. -/
noncomputable def paperInt (f : ℝ × ℝ × ℝ × ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1, f (t, a, b, c)

/-- The paper's smooth periodic fields: `C^∞` with `f(p + eₖ) = f(p)`. -/
def paperSmooth (f : ℝ × ℝ × ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ k p, f (p + paperE k) = f p

/-- The repository's statements (`Smooth.enstrophy_identity_smooth` and
`Smooth.weighted_identity_smooth`), under the common hypotheses (div), (vort), (wt). -/
def formal_claim : Prop :=
  ∀ (ν : ℝ) (u w : Fin 3 → Smooth.A) (φ : Smooth.A),
    WeightedEnstrophy.div Smooth.setting u = 0 → VorticityEq Smooth.setting ν u w →
    WeightEq Smooth.setting u w φ →
    deriv (Smooth.I (vsq w)) =
        (2 : ℝ) • Smooth.I (stretch Smooth.setting u w) - (2 * ν) • Smooth.I (gradSq Smooth.setting w)
      ∧ deriv (Smooth.I (vsq w * vsq w * φ)) =
        (4 : ℝ) • Smooth.I (vsq w * φ * stretch Smooth.setting u w)
        + (4 * ν) • Smooth.I (vsq w * φ * wLapW Smooth.setting w)
        + Smooth.I (vsq w * vsq w * vsq w)

/-- The paper's smooth-model theorem: identities (1) and (2) for all `u, ω, φ ∈ A` satisfying
(div)–(wt). (1): `dE/dt = P - ν ∫|∇ω|²`, `E = ½∫|ω|²`, `P = ∫ωᵢωⱼ∂ⱼuᵢ`.
(2): `dQ/dt = 4∫|ω|²φ ω·(ω·∇)u + 4ν∫|ω|²φ ω·Δω + ∫|ω|⁶`, `Q = ∫|ω|⁴φ`. -/
def paper_claim : Prop :=
  ∀ (ν : ℝ) (u w : Fin 3 → ℝ × ℝ × ℝ × ℝ → ℝ) (φ : ℝ × ℝ × ℝ × ℝ → ℝ),
    (∀ i, paperSmooth (u i)) → (∀ i, paperSmooth (w i)) → paperSmooth φ →
    (∀ p, ∑ k, fderiv ℝ (u k) p (paperE k) = 0) →
    (∀ i p, fderiv ℝ (w i) p (1, 0, 0, 0) =
      -(∑ k, u k p * fderiv ℝ (w i) p (paperE k)) + ∑ k, w k p * fderiv ℝ (u i) p (paperE k)
        + ν * ∑ k, fderiv ℝ (fun q => fderiv ℝ (w i) q (paperE k)) p (paperE k)) →
    (∀ p, fderiv ℝ φ p (1, 0, 0, 0) =
      -(∑ k, u k p * fderiv ℝ φ p (paperE k)) + ∑ i, w i p ^ 2) →
    ∀ t,
      deriv (fun s => (1 / 2 : ℝ) * paperInt (fun p => ∑ i, w i p ^ 2) s) t =
        paperInt (fun p => ∑ i, ∑ j, w i p * w j p * fderiv ℝ (u i) p (paperE j)) t
          - ν * paperInt (fun p => ∑ i, ∑ k, fderiv ℝ (w i) p (paperE k) ^ 2) t
      ∧ deriv (paperInt (fun p => (∑ i, w i p ^ 2) ^ 2 * φ p)) t =
        4 * paperInt (fun p => (∑ i, w i p ^ 2) * φ p *
              ∑ i, w i p * ∑ j, w j p * fderiv ℝ (u i) p (paperE j)) t
          + 4 * ν * paperInt (fun p => (∑ i, w i p ^ 2) * φ p *
              ∑ i, w i p * ∑ k, fderiv ℝ (fun q => fderiv ℝ (w i) q (paperE k)) p (paperE k)) t
          + paperInt (fun p => (∑ i, w i p ^ 2) ^ 3) t

theorem e_eq (k : Fin 3) : Smooth.e k = paperE k := by
  fin_cases k <;> rfl

theorem coe_sum3 (s : Fin 3 → Smooth.A) :
    ((∑ k, s k : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) = ∑ k, (s k : ℝ × ℝ × ℝ × ℝ → ℝ) := by
  simp

theorem coe_d (k : Fin 3) (f : Smooth.A) :
    ((Smooth.setting.d k f : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) =
      fun q => fderiv ℝ (f : ℝ × ℝ × ℝ × ℝ → ℝ) q (paperE k) := by
  funext q
  rw [← e_eq]
  rfl

theorem coe_dt (f : Smooth.A) :
    ((Smooth.setting.dt f : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) =
      fun q => fderiv ℝ (f : ℝ × ℝ × ℝ × ℝ → ℝ) q (1, 0, 0, 0) := rfl

theorem I_eq (f : Smooth.A) : Smooth.I f = paperInt (f : ℝ × ℝ × ℝ × ℝ → ℝ) := rfl

theorem div_iff (u : Fin 3 → Smooth.A) :
    WeightedEnstrophy.div Smooth.setting u = 0 ↔
      ∀ p, ∑ k, fderiv ℝ (u k : ℝ × ℝ × ℝ × ℝ → ℝ) p (paperE k) = 0 := by
  rw [← Subtype.coe_inj, funext_iff]
  simp [WeightedEnstrophy.div, coe_d, Finset.sum_apply]

theorem vort_iff (ν : ℝ) (u w : Fin 3 → Smooth.A) :
    VorticityEq Smooth.setting ν u w ↔
      ∀ i p, fderiv ℝ (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p (1, 0, 0, 0) =
        -(∑ k, (u k : ℝ × ℝ × ℝ × ℝ → ℝ) p * fderiv ℝ (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p (paperE k))
          + ∑ k, (w k : ℝ × ℝ × ℝ × ℝ → ℝ) p * fderiv ℝ (u i : ℝ × ℝ × ℝ × ℝ → ℝ) p (paperE k)
          + ν * ∑ k, fderiv ℝ (fun q => fderiv ℝ (w i : ℝ × ℝ × ℝ × ℝ → ℝ) q (paperE k)) p
              (paperE k) := by
  unfold VorticityEq
  refine forall_congr' fun i => ?_
  rw [← Subtype.coe_inj, funext_iff]
  simp [WeightedEnstrophy.adv, WeightedEnstrophy.lap, coe_d, coe_dt, Finset.sum_apply,
    Finset.mul_sum]

theorem vsq_coe (w : Fin 3 → Smooth.A) :
    ((vsq w : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) = fun p => ∑ i, (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p ^ 2 := by
  funext p
  simp [vsq, Finset.sum_apply, pow_two]

theorem stretch_coe (u w : Fin 3 → Smooth.A) :
    ((stretch Smooth.setting u w : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) = fun p =>
      ∑ i, ∑ j, (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p * (w j : ℝ × ℝ × ℝ × ℝ → ℝ) p *
        fderiv ℝ (u i : ℝ × ℝ × ℝ × ℝ → ℝ) p (paperE j) := by
  funext p
  simp [stretch, coe_d, Finset.sum_apply]

theorem gradSq_coe (w : Fin 3 → Smooth.A) :
    ((gradSq Smooth.setting w : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) = fun p =>
      ∑ i, ∑ k, fderiv ℝ (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p (paperE k) ^ 2 := by
  funext p
  simp [gradSq, coe_d, Finset.sum_apply, pow_two]

/-- Package a paper field as an element of `Smooth.A`. -/
def toA (f : ℝ × ℝ × ℝ × ℝ → ℝ) (hf : paperSmooth f) : Smooth.A :=
  ⟨f, hf.1, fun k p => by rw [e_eq]; exact hf.2 k p⟩

theorem coe_toA (f : ℝ × ℝ × ℝ × ℝ → ℝ) (hf : paperSmooth f) :
    ((toA f hf : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) = f := rfl

theorem fromA (f : Smooth.A) : paperSmooth (f : ℝ × ℝ × ℝ × ℝ → ℝ) :=
  ⟨Smooth.smooth f, fun k p => by rw [← e_eq]; exact Smooth.periodic f k p⟩

/-- The paper's `d/dt (½ ∫|w|²)` is half of `d/dt ∫|w|²`. -/
theorem deriv_half (F : ℝ → ℝ) (t : ℝ) :
    deriv (fun s => (1 / 2 : ℝ) * F s) t = (1 / 2 : ℝ) * deriv F t := by
  simp [deriv_const_mul_field']

theorem weight_iff (u w : Fin 3 → Smooth.A) (φ : Smooth.A) :
    WeightEq Smooth.setting u w φ ↔
      ∀ p, fderiv ℝ (φ : ℝ × ℝ × ℝ × ℝ → ℝ) p (1, 0, 0, 0) =
        -(∑ k, (u k : ℝ × ℝ × ℝ × ℝ → ℝ) p * fderiv ℝ (φ : ℝ × ℝ × ℝ × ℝ → ℝ) p (paperE k))
          + ∑ i, (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p ^ 2 := by
  unfold WeightEq
  rw [← Subtype.coe_inj, funext_iff]
  simp [WeightedEnstrophy.adv, coe_d, coe_dt, vsq_coe, Finset.sum_apply]

theorem Q_coe (w : Fin 3 → Smooth.A) (φ : Smooth.A) :
    ((vsq w * vsq w * φ : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) = fun p =>
      (∑ i, (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p ^ 2) ^ 2 * (φ : ℝ × ℝ × ℝ × ℝ → ℝ) p := by
  funext p
  simp only [Subalgebra.coe_mul, Pi.mul_apply, vsq_coe]
  ring

theorem T1_coe (u w : Fin 3 → Smooth.A) (φ : Smooth.A) :
    ((vsq w * φ * stretch Smooth.setting u w : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) = fun p =>
      (∑ i, (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p ^ 2) * (φ : ℝ × ℝ × ℝ × ℝ → ℝ) p *
        ∑ i, (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p * ∑ j, (w j : ℝ × ℝ × ℝ × ℝ → ℝ) p *
          fderiv ℝ (u i : ℝ × ℝ × ℝ × ℝ → ℝ) p (paperE j) := by
  funext p
  simp only [Subalgebra.coe_mul, Pi.mul_apply, vsq_coe, stretch_coe]
  simp only [Fin.sum_univ_three]
  ring

theorem wLapW_coe (w : Fin 3 → Smooth.A) :
    ((wLapW Smooth.setting w : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) = fun p =>
      ∑ i, (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p *
        ∑ k, fderiv ℝ (fun q => fderiv ℝ (w i : ℝ × ℝ × ℝ × ℝ → ℝ) q (paperE k)) p (paperE k) := by
  funext p
  simp [wLapW, WeightedEnstrophy.lap, coe_d, Finset.sum_apply]

theorem T2_coe (w : Fin 3 → Smooth.A) (φ : Smooth.A) :
    ((vsq w * φ * wLapW Smooth.setting w : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) = fun p =>
      (∑ i, (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p ^ 2) * (φ : ℝ × ℝ × ℝ × ℝ → ℝ) p *
        ∑ i, (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p *
          ∑ k, fderiv ℝ (fun q => fderiv ℝ (w i : ℝ × ℝ × ℝ × ℝ → ℝ) q (paperE k)) p (paperE k) := by
  funext p
  simp only [Subalgebra.coe_mul, Pi.mul_apply, vsq_coe, wLapW_coe]

theorem S6_coe (w : Fin 3 → Smooth.A) :
    ((vsq w * vsq w * vsq w : Smooth.A) : ℝ × ℝ × ℝ × ℝ → ℝ) = fun p =>
      (∑ i, (w i : ℝ × ℝ × ℝ × ℝ → ℝ) p ^ 2) ^ 3 := by
  funext p
  simp only [Subalgebra.coe_mul, Pi.mul_apply, vsq_coe]
  ring

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro h ν u w φ hu hw hφ hdiv hvort hwt t
    let U : Fin 3 → Smooth.A := fun i => toA (u i) (hu i)
    let W : Fin 3 → Smooth.A := fun i => toA (w i) (hw i)
    let Φ : Smooth.A := toA φ hφ
    obtain ⟨k1, k2⟩ := h ν U W Φ ((div_iff U).2 hdiv) ((vort_iff ν U W).2 hvort)
      ((weight_iff U W Φ).2 hwt)
    have key := congrFun k1 t
    have key2 := congrFun k2 t
    rw [I_eq, I_eq, I_eq, vsq_coe, stretch_coe, gradSq_coe] at key
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, U, W, coe_toA] at key
    rw [I_eq, I_eq, I_eq, I_eq, Q_coe, T1_coe, T2_coe, S6_coe] at key2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, U, W, Φ, coe_toA] at key2
    refine ⟨?_, ?_⟩
    · rw [deriv_half]
      linear_combination (1 / 2 : ℝ) * key
    · rw [key2]
  · intro h ν u w φ hu hw hφ
    have hP := fun t => h ν (fun i => (u i : ℝ × ℝ × ℝ × ℝ → ℝ))
      (fun i => (w i : ℝ × ℝ × ℝ × ℝ → ℝ)) (φ : ℝ × ℝ × ℝ × ℝ → ℝ)
      (fun i => fromA (u i)) (fun i => fromA (w i)) (fromA φ) ((div_iff u).1 hu)
      ((vort_iff ν u w).1 hw) ((weight_iff u w φ).1 hφ) t
    refine ⟨?_, ?_⟩
    · funext t
      have key := (hP t).1
      rw [deriv_half] at key
      rw [I_eq, I_eq, I_eq, vsq_coe, stretch_coe, gradSq_coe]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (2 : ℝ) * key
    · funext t
      have key := (hP t).2
      rw [I_eq, I_eq, I_eq, I_eq, Q_coe, T1_coe, T2_coe, S6_coe]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [key]
-- TRUTH-GATE LOCK END

/-- The repository's theorems prove `formal_claim`. -/
theorem formal_claim_holds : formal_claim := by
  intro ν u w φ hu hw hφ
  exact ⟨enstrophy_identity_smooth ν u w hu hw, weighted_identity_smooth ν u w φ hu hw hφ⟩

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

/-! ### Non-vacuity witness

The hypotheses of `paper_claim` are satisfiable by a non-trivial configuration:
`ν = 0`, `u = 0`, `ω = (1, 0, 0)` (constant), `φ(t, a, b, c) = t`. Then (div) and (vort) hold
trivially and (wt) reads `∂ₜφ = 1 = |ω|²`. Identity (2) then says `dQ/dt = ∫|ω|⁶ = 1` with
`Q(t) = ∫ t = t`, and `φ` is not constant, so the weighted identity is exercised. -/

/-- The witness fields. -/
def witnessU : Fin 3 → ℝ × ℝ × ℝ × ℝ → ℝ := fun _ _ => 0
def witnessW : Fin 3 → ℝ × ℝ × ℝ × ℝ → ℝ := fun i _ => if i = 0 then 1 else 0
def witnessPhi : ℝ × ℝ × ℝ × ℝ → ℝ := fun p => p.1

theorem nonvacuity_witness :
    (∀ i, paperSmooth (witnessU i)) ∧ (∀ i, paperSmooth (witnessW i)) ∧ paperSmooth witnessPhi ∧
    (∀ p, ∑ k, fderiv ℝ (witnessU k) p (paperE k) = 0) ∧
    (∀ i p, fderiv ℝ (witnessW i) p (1, 0, 0, 0) =
      -(∑ k, witnessU k p * fderiv ℝ (witnessW i) p (paperE k))
        + ∑ k, witnessW k p * fderiv ℝ (witnessU i) p (paperE k)
        + (0 : ℝ) * ∑ k, fderiv ℝ (fun q => fderiv ℝ (witnessW i) q (paperE k)) p (paperE k)) ∧
    (∀ p, fderiv ℝ witnessPhi p (1, 0, 0, 0) =
      -(∑ k, witnessU k p * fderiv ℝ witnessPhi p (paperE k)) + ∑ i, witnessW i p ^ 2) := by
  have hW : ∀ i, witnessW i = fun _ => if i = 0 then (1 : ℝ) else 0 := fun i => rfl
  have hU : ∀ i, witnessU i = fun _ => (0 : ℝ) := fun i => rfl
  have hPhi : fderiv ℝ witnessPhi = fun _ => ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ) := by
    funext p; exact (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ)).fderiv
  refine ⟨fun i => ⟨contDiff_const, fun _ _ => rfl⟩, fun i => ⟨contDiff_const, fun _ _ => rfl⟩,
    ⟨(ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ × ℝ)).contDiff, fun k p => ?_⟩, fun p => ?_,
    fun i p => ?_, fun p => ?_⟩
  · fin_cases k <;> simp [witnessPhi, paperE]
  · simp [hU]
  · simp [hU, hW]
  · rw [hPhi]; simp [hU, witnessW]

end TruthGate
