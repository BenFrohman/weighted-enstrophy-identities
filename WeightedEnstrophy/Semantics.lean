/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import WeightedEnstrophy.Smooth

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/main.tex
PAPER_SECTION: Theorem "Identity (1)" (Section "Identity (1)") in the smooth periodic model (Section "Smooth periodic fields", theorem `Smooth.enstrophy_identity_smooth`), with the Setting equations (div) and (vort)
PAPER_SHA256: c23af493e94fb06598dc46b354bd692b977352aebcfd344bd701a2acaa0cd754

Locked paper claim, quoted verbatim (the identity, the smooth-model theorem, then the paper's
definitions it uses):

PAPER_QUOTE_BEGIN
\begin{theorem}[Identity (1), \texttt{enstrophy\_identity}, \texttt{enstrophy\_identity\_T3}]
With $E=\frac12\int|\omega|^2$ and $P=\int\omega_i\omega_j\partial_ju_i$,
\[\frac{dE}{dt}=P-\nu\int_{\mathbb{T}^3}|\nabla\omega|^2 .\]
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
* hypotheses: (div) `∂ₖuₖ = 0` and (vort) `∂ₜωᵢ = -uₖ∂ₖωᵢ + ωₖ∂ₖuᵢ + ν∂ₖ∂ₖωᵢ`, pointwise;
* the conclusion is the paper's displayed form `dE/dt = P - ν∫|∇ω|²` with `E = ½∫|ω|²`, at every `t`.

`formal_claim` is the statement of `WeightedEnstrophy.Smooth.enstrophy_identity_smooth`, phrased in
the repository's subalgebra `Smooth.A` with `div`, `VorticityEq`, `vsq`, `stretch`, `gradSq` and
the factor-2 form `D_t I(|ω|²) = 2 I(…) - 2ν I(…)`. `paper_claim` uses plain functions, `fderiv` and
iterated interval integrals. The correspondence packages functions into `Smooth.A` and back and
converts the factor-2 form into the paper's `E = ½∫|ω|²` form.

Scope: an exact identity for smooth periodic solutions of (div) and (vort). It gives no bound
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

/-- The repository's statement (`Smooth.enstrophy_identity_smooth`). -/
def formal_claim : Prop :=
  ∀ (ν : ℝ) (u w : Fin 3 → Smooth.A),
    WeightedEnstrophy.div Smooth.setting u = 0 → VorticityEq Smooth.setting ν u w →
    deriv (Smooth.I (vsq w)) =
      (2 : ℝ) • Smooth.I (stretch Smooth.setting u w) - (2 * ν) • Smooth.I (gradSq Smooth.setting w)

/-- Paper Identity (1) for smooth periodic fields: `dE/dt = P - ν ∫|∇w|²`, `E = ½∫|w|²`. -/
def paper_claim : Prop :=
  ∀ (ν : ℝ) (u w : Fin 3 → ℝ × ℝ × ℝ × ℝ → ℝ),
    (∀ i, paperSmooth (u i)) → (∀ i, paperSmooth (w i)) →
    (∀ p, ∑ k, fderiv ℝ (u k) p (paperE k) = 0) →
    (∀ i p, fderiv ℝ (w i) p (1, 0, 0, 0) =
      -(∑ k, u k p * fderiv ℝ (w i) p (paperE k)) + ∑ k, w k p * fderiv ℝ (u i) p (paperE k)
        + ν * ∑ k, fderiv ℝ (fun q => fderiv ℝ (w i) q (paperE k)) p (paperE k)) →
    ∀ t, deriv (fun s => (1 / 2 : ℝ) * paperInt (fun p => ∑ i, w i p ^ 2) s) t =
      paperInt (fun p => ∑ i, ∑ j, w i p * w j p * fderiv ℝ (u i) p (paperE j)) t
        - ν * paperInt (fun p => ∑ i, ∑ k, fderiv ℝ (w i) p (paperE k) ^ 2) t

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

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro h ν u w hu hw hdiv hvort t
    let U : Fin 3 → Smooth.A := fun i => toA (u i) (hu i)
    let W : Fin 3 → Smooth.A := fun i => toA (w i) (hw i)
    have key := congrFun (h ν U W ((div_iff U).2 hdiv) ((vort_iff ν U W).2 hvort)) t
    rw [I_eq, I_eq, I_eq, vsq_coe, stretch_coe, gradSq_coe] at key
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, U, W, coe_toA] at key
    rw [deriv_half]
    linear_combination (1 / 2 : ℝ) * key
  · intro h ν u w hu hw
    funext t
    have key := h ν (fun i => (u i : ℝ × ℝ × ℝ × ℝ → ℝ)) (fun i => (w i : ℝ × ℝ × ℝ × ℝ → ℝ))
      (fun i => fromA (u i)) (fun i => fromA (w i)) ((div_iff u).1 hu) ((vort_iff ν u w).1 hw) t
    rw [deriv_half] at key
    rw [I_eq, I_eq, I_eq, vsq_coe, stretch_coe, gradSq_coe]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (2 : ℝ) * key
-- TRUTH-GATE LOCK END

/-- The repository's theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim := by
  intro ν u w hu hw
  exact enstrophy_identity_smooth ν u w hu hw

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
