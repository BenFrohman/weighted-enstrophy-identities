/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# Enstrophy and weighted-enstrophy identities in a periodic differential algebra

`A` is a commutative `K`-algebra of (time-dependent) periodic fields with three spatial
derivations `∂ k` and a time derivation `∂t`. `I : A →ₗ[K] B` is the spatial integral over the
torus; it kills every spatial derivative (periodicity) and satisfies `I (∂t f) = Dt (I f)`.
-/

open Finset

namespace WeightedEnstrophy

variable {K A B : Type*} [CommRing K] [CommRing A] [Algebra K A] [AddCommGroup B] [Module K B]

/-- A periodic differential setting on the 3-torus. -/
structure PeriodicSetting (K A B : Type*) [CommRing K] [CommRing A] [Algebra K A]
    [AddCommGroup B] [Module K B] where
  d : Fin 3 → Derivation K A A
  dt : Derivation K A A
  I : A →ₗ[K] B
  Dt : B → B
  int_d : ∀ k f, I (d k f) = 0
  int_dt : ∀ f, I (dt f) = Dt (I f)

variable (S : PeriodicSetting K A B)

/-- `|ω|² = Σ ωᵢωᵢ`. -/
def vsq (w : Fin 3 → A) : A := ∑ i, w i * w i
/-- `(u·∇) f`. -/
def adv (u : Fin 3 → A) (f : A) : A := ∑ k, u k * S.d k f
/-- `Δ f`. -/
def lap (f : A) : A := ∑ k, S.d k (S.d k f)
/-- `div u`. -/
def div (u : Fin 3 → A) : A := ∑ k, S.d k (u k)
/-- `ωᵢ ωⱼ ∂ⱼ uᵢ`, the stretching density. -/
def stretch (u w : Fin 3 → A) : A := ∑ i, ∑ j, w i * w j * S.d j (u i)
/-- `|∇ω|²`. -/
def gradSq (w : Fin 3 → A) : A := ∑ i, ∑ k, S.d k (w i) * S.d k (w i)
/-- `ω · Δω`. -/
def wLapW (w : Fin 3 → A) : A := ∑ i, w i * lap S (w i)

/-- Vorticity equation `∂t ω + (u·∇)ω = (ω·∇)u + ν Δω`. -/
def VorticityEq (ν : K) (u w : Fin 3 → A) : Prop :=
  ∀ i, S.dt (w i) = - adv S u (w i) + adv S w (u i) + ν • lap S (w i)

/-- Transport equation for the weight: `∂t φ + u·∇φ = |ω|²`. -/
def WeightEq (u w : Fin 3 → A) (φ : A) : Prop :=
  S.dt φ = - adv S u φ + vsq w

lemma I_sum_d (F : Fin 3 → A) : S.I (∑ k, S.d k (F k)) = 0 := by
  simp [map_sum, S.int_d]

/-- Pointwise: `(u·∇) g = Σₖ ∂ₖ(uₖ g) − (div u) g`. -/
lemma adv_eq (u : Fin 3 → A) (g : A) :
    adv S u g = ∑ k, S.d k (u k * g) - div S u * g := by
  simp only [adv, div, map_add, Derivation.leibniz, smul_eq_mul, Fin.sum_univ_three]; ring

/-- Divergence lemma for transport: `∫ (u·∇) g = 0` when `div u = 0`. -/
theorem int_adv_eq_zero (u : Fin 3 → A) (hu : div S u = 0) (g : A) :
    S.I (adv S u g) = 0 := by
  rw [adv_eq, hu, zero_mul, sub_zero, I_sum_d]

/-- Pointwise: `ω·Δω = Σₖ ∂ₖ(Σᵢ ωᵢ ∂ₖωᵢ) − |∇ω|²`. -/
lemma wLapW_eq (w : Fin 3 → A) :
    wLapW S w = ∑ k, S.d k (∑ i, w i * S.d k (w i)) - gradSq S w := by
  simp only [wLapW, lap, gradSq, map_sum, map_add, Derivation.leibniz, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- Pointwise: `Σᵢ ωᵢ (u·∇)ωᵢ = (u·∇)(½|ω|²)` in the form `2·Σᵢ ωᵢ (u·∇)ωᵢ = (u·∇)|ω|²`. -/
lemma two_w_adv (u w : Fin 3 → A) :
    2 * ∑ i, w i * adv S u (w i) = adv S u (vsq w) := by
  simp only [adv, vsq, map_sum, map_add, Derivation.leibniz, smul_eq_mul, Fin.sum_univ_three]; ring

/-- **Identity (1), pointwise form.** -/
lemma dt_half_sq (ν : K) (u w : Fin 3 → A) (hw : VorticityEq S ν u w) :
    S.dt (vsq w) = 2 * stretch S u w + (2 * algebraMap K A ν) * wLapW S w
      - 2 * ∑ i, w i * adv S u (w i) := by
  unfold VorticityEq at hw
  simp only [vsq, map_add, Derivation.leibniz, smul_eq_mul, hw, stretch, wLapW, adv,
    Algebra.smul_def, Fin.sum_univ_three]
  ring

/-- Identity (1) before integration: the time derivative of `|ω|²` is the stretching and
dissipation densities plus a spatial divergence. -/
lemma dt_vsq_div (ν : K) (u w : Fin 3 → A) (hu : div S u = 0) (hw : VorticityEq S ν u w) :
    S.dt (vsq w) = (2 : K) • stretch S u w - (2 * ν) • gradSq S w
      + ∑ k, S.d k ((2 * ν) • (∑ i, w i * S.d k (w i)) - u k * vsq w) := by
  rw [dt_half_sq S ν u w hw, two_w_adv, wLapW_eq, adv_eq, hu]
  simp only [map_sub, Derivation.map_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
    mul_comm (u _) (vsq w)]
  simp only [Algebra.smul_def, map_mul, map_ofNat]
  ring

/-- **Identity (1).** For `E = ½∫|ω|²` (stated as `2E = ∫|ω|²`):
`d/dt ∫|ω|² = 2 ∫ ωᵢωⱼ∂ⱼuᵢ − 2ν ∫|∇ω|²`, i.e. `dE/dt = P − ν∫|∇ω|²`. -/
theorem enstrophy_identity (ν : K) (u w : Fin 3 → A) (hu : div S u = 0)
    (hw : VorticityEq S ν u w) :
    S.Dt (S.I (vsq w)) = (2 : K) • S.I (stretch S u w) - (2 * ν) • S.I (gradSq S w) := by
  rw [← S.int_dt, dt_vsq_div S ν u w hu hw, map_add, I_sum_d, add_zero, map_sub, map_smul,
    map_smul]

/-- **Identity (2), pointwise form**, with `s = |ω|²`. -/
lemma dt_weighted (ν : K) (u w : Fin 3 → A) (φ : A) (hw : VorticityEq S ν u w)
    (hφ : WeightEq S u w φ) :
    S.dt (vsq w * vsq w * φ) =
      4 * (vsq w * φ * stretch S u w) + 4 * algebraMap K A ν * (vsq w * φ * wLapW S w)
      + vsq w * vsq w * vsq w - adv S u (vsq w * vsq w * φ) := by
  have hs : S.dt (vsq w) = 2 * stretch S u w + (2 * algebraMap K A ν) * wLapW S w
      - adv S u (vsq w) := by rw [dt_half_sq S ν u w hw, two_w_adv]
  have hadv : adv S u (vsq w * vsq w * φ)
      = 2 * vsq w * φ * adv S u (vsq w) + vsq w * vsq w * adv S u φ := by
    simp only [adv, Derivation.leibniz, smul_eq_mul, Fin.sum_univ_three]; ring
  unfold WeightEq at hφ
  rw [hadv]
  simp only [Derivation.leibniz, smul_eq_mul, hs, hφ]
  ring

/-- Identity (2) before integration: a spatial divergence carries the transport terms. -/
lemma dt_weighted_div (ν : K) (u w : Fin 3 → A) (φ : A) (hu : div S u = 0)
    (hw : VorticityEq S ν u w) (hφ : WeightEq S u w φ) :
    S.dt (vsq w * vsq w * φ) =
      (4 : K) • (vsq w * φ * stretch S u w) + (4 * ν) • (vsq w * φ * wLapW S w)
      + vsq w * vsq w * vsq w - ∑ k, S.d k (u k * (vsq w * vsq w * φ)) := by
  rw [dt_weighted S ν u w φ hw hφ, adv_eq, hu]
  simp only [Algebra.smul_def, map_mul, map_ofNat]
  ring

/-- **Identity (2).** For `Q = ∫|ω|⁴φ`:
`dQ/dt = 4∫|ω|²φ ω·(ω·∇)u + 4ν∫|ω|²φ ω·Δω + ∫|ω|⁶`. -/
theorem weighted_identity (ν : K) (u w : Fin 3 → A) (φ : A) (hu : div S u = 0)
    (hw : VorticityEq S ν u w) (hφ : WeightEq S u w φ) :
    S.Dt (S.I (vsq w * vsq w * φ)) =
      (4 : K) • S.I (vsq w * φ * stretch S u w)
      + (4 * ν) • S.I (vsq w * φ * wLapW S w)
      + S.I (vsq w * vsq w * vsq w) := by
  rw [← S.int_dt, dt_weighted_div S ν u w φ hu hw hφ, map_sub, I_sum_d, sub_zero, map_add,
    map_add, map_smul, map_smul]

/-- `ω·(ω·∇)u` equals the stretching density, so (2) is the paper's form. -/
lemma stretch_eq (u w : Fin 3 → A) : stretch S u w = ∑ i, w i * adv S w (u i) := by
  simp only [stretch, adv, Finset.mul_sum]; refine sum_congr rfl fun i _ => sum_congr rfl ?_
  intro j _; ring

end WeightedEnstrophy
