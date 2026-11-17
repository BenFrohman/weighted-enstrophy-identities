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

variable (setting : PeriodicSetting K A B)

/-- `|ω|² = Σ ωᵢωᵢ`. -/
def vsq (ω : Fin 3 → A) : A := ∑ i, ω i * ω i
/-- `(u·∇) f`. -/
def adv (u : Fin 3 → A) (f : A) : A := ∑ k, u k * setting.d k f
/-- `Δ f`. -/
def lap (f : A) : A := ∑ k, setting.d k (setting.d k f)
/-- `div u`. -/
def div (u : Fin 3 → A) : A := ∑ k, setting.d k (u k)
/-- `ωᵢ ωⱼ ∂ⱼ uᵢ`, the stretching density. -/
def stretch (u ω : Fin 3 → A) : A := ∑ i, ∑ j, ω i * ω j * setting.d j (u i)
/-- `|∇ω|²`. -/
def gradSq (ω : Fin 3 → A) : A := ∑ i, ∑ k, setting.d k (ω i) * setting.d k (ω i)
/-- `ω · Δω`. -/
def wLapW (ω : Fin 3 → A) : A := ∑ i, ω i * lap setting (ω i)

/-- Vorticity equation `∂t ω + (u·∇)ω = (ω·∇)u + ν Δω`. -/
def VorticityEq (ν : K) (u ω : Fin 3 → A) : Prop :=
  ∀ i, setting.dt (ω i) = - adv setting u (ω i) + adv setting ω (u i) + ν • lap setting (ω i)

/-- Transport equation for the weight: `∂t φ + u·∇φ = |ω|²`. -/
def WeightEq (u ω : Fin 3 → A) (φ : A) : Prop :=
  setting.dt φ = - adv setting u φ + vsq ω

lemma I_sum_d (F : Fin 3 → A) : setting.I (∑ k, setting.d k (F k)) = 0 := by
  simp [map_sum, setting.int_d]

/-- Pointwise: `(u·∇) g = Σₖ ∂ₖ(uₖ g) − (div u) g`. -/
lemma adv_eq (u : Fin 3 → A) (g : A) :
    adv setting u g = ∑ k, setting.d k (u k * g) - div setting u * g := by
  simp only [adv, div, map_add, Derivation.leibniz, smul_eq_mul, Fin.sum_univ_three]; ring

/-- Divergence lemma for transport: `∫ (u·∇) g = 0` when `div u = 0`. -/
theorem int_adv_eq_zero (u : Fin 3 → A) (hu : div setting u = 0) (g : A) :
    setting.I (adv setting u g) = 0 := by
  rw [adv_eq, hu, zero_mul, sub_zero, I_sum_d]

/-- Pointwise: `ω·Δω = Σₖ ∂ₖ(Σᵢ ωᵢ ∂ₖωᵢ) − |∇ω|²`. -/
lemma wLapW_eq (ω : Fin 3 → A) :
    wLapW setting ω = ∑ k, setting.d k (∑ i, ω i * setting.d k (ω i)) - gradSq setting ω := by
  simp only [wLapW, lap, gradSq, map_sum, map_add, Derivation.leibniz, smul_eq_mul, Fin.sum_univ_three]
  ring

/-- Pointwise: `Σᵢ ωᵢ (u·∇)ωᵢ = (u·∇)(½|ω|²)` in the form `2·Σᵢ ωᵢ (u·∇)ωᵢ = (u·∇)|ω|²`. -/
lemma two_w_adv (u ω : Fin 3 → A) :
    2 * ∑ i, ω i * adv setting u (ω i) = adv setting u (vsq ω) := by
  simp only [adv, vsq, map_sum, map_add, Derivation.leibniz, smul_eq_mul, Fin.sum_univ_three]; ring

/-- **Identity (1), pointwise form.** -/
lemma dt_half_sq (ν : K) (u ω : Fin 3 → A) (hw : VorticityEq setting ν u ω) :
    setting.dt (vsq ω) = 2 * stretch setting u ω + (2 * algebraMap K A ν) * wLapW setting ω
      - 2 * ∑ i, ω i * adv setting u (ω i) := by
  unfold VorticityEq at hw
  simp only [vsq, map_add, Derivation.leibniz, smul_eq_mul, hw, stretch, wLapW, adv,
    Algebra.smul_def, Fin.sum_univ_three]
  ring

/-- Identity (1) before integration: the time derivative of `|ω|²` is the stretching and
dissipation densities plus a spatial divergence. -/
lemma dt_vsq_div (ν : K) (u ω : Fin 3 → A) (hu : div setting u = 0) (hw : VorticityEq setting ν u ω) :
    setting.dt (vsq ω) = (2 : K) • stretch setting u ω - (2 * ν) • gradSq setting ω
      + ∑ k, setting.d k ((2 * ν) • (∑ i, ω i * setting.d k (ω i)) - u k * vsq ω) := by
  rw [dt_half_sq setting ν u ω hw, two_w_adv, wLapW_eq, adv_eq, hu]
  simp only [map_sub, Derivation.map_smul, Finset.sum_sub_distrib, ← Finset.smul_sum,
    mul_comm (u _) (vsq ω)]
  simp only [Algebra.smul_def, map_mul, map_ofNat]
  ring

/-- **Identity (1).** For the enstrophy `‖ω‖²_{L²} = ∫|ω|²`:
`d/dt ∫|ω|² = 2 ∫ ωᵢωⱼ∂ⱼuᵢ − 2ν ∫|∇ω|²`, i.e. `d/dt (½‖ω‖²_{L²}) = ∫ ωᵢωⱼ∂ⱼuᵢ − ν‖∇ω‖²_{L²}`. -/
theorem enstrophy_identity (ν : K) (u ω : Fin 3 → A) (hu : div setting u = 0)
    (hw : VorticityEq setting ν u ω) :
    setting.Dt (setting.I (vsq ω)) = (2 : K) • setting.I (stretch setting u ω) - (2 * ν) • setting.I (gradSq setting ω) := by
  rw [← setting.int_dt, dt_vsq_div setting ν u ω hu hw, map_add, I_sum_d, add_zero, map_sub, map_smul,
    map_smul]

/-- **Identity (2), pointwise form** (`|ω|⁴φ = |ω|²·|ω|²·φ`). -/
lemma dt_weighted (ν : K) (u ω : Fin 3 → A) (φ : A) (hw : VorticityEq setting ν u ω)
    (hφ : WeightEq setting u ω φ) :
    setting.dt (vsq ω * vsq ω * φ) =
      4 * (vsq ω * φ * stretch setting u ω) + 4 * algebraMap K A ν * (vsq ω * φ * wLapW setting ω)
      + vsq ω * vsq ω * vsq ω - adv setting u (vsq ω * vsq ω * φ) := by
  have hs : setting.dt (vsq ω) = 2 * stretch setting u ω + (2 * algebraMap K A ν) * wLapW setting ω
      - adv setting u (vsq ω) := by rw [dt_half_sq setting ν u ω hw, two_w_adv]
  have hadv : adv setting u (vsq ω * vsq ω * φ)
      = 2 * vsq ω * φ * adv setting u (vsq ω) + vsq ω * vsq ω * adv setting u φ := by
    simp only [adv, Derivation.leibniz, smul_eq_mul, Fin.sum_univ_three]; ring
  unfold WeightEq at hφ
  rw [hadv]
  simp only [Derivation.leibniz, smul_eq_mul, hs, hφ]
  ring

/-- Identity (2) before integration: a spatial divergence carries the transport terms. -/
lemma dt_weighted_div (ν : K) (u ω : Fin 3 → A) (φ : A) (hu : div setting u = 0)
    (hw : VorticityEq setting ν u ω) (hφ : WeightEq setting u ω φ) :
    setting.dt (vsq ω * vsq ω * φ) =
      (4 : K) • (vsq ω * φ * stretch setting u ω) + (4 * ν) • (vsq ω * φ * wLapW setting ω)
      + vsq ω * vsq ω * vsq ω - ∑ k, setting.d k (u k * (vsq ω * vsq ω * φ)) := by
  rw [dt_weighted setting ν u ω φ hw hφ, adv_eq, hu]
  simp only [Algebra.smul_def, map_mul, map_ofNat]
  ring

/-- **Identity (2).**
`d/dt ∫|ω|⁴φ = 4∫|ω|²φ ω·(ω·∇)u + 4ν∫|ω|²φ ω·Δω + ∫|ω|⁶`. -/
theorem weighted_identity (ν : K) (u ω : Fin 3 → A) (φ : A) (hu : div setting u = 0)
    (hw : VorticityEq setting ν u ω) (hφ : WeightEq setting u ω φ) :
    setting.Dt (setting.I (vsq ω * vsq ω * φ)) =
      (4 : K) • setting.I (vsq ω * φ * stretch setting u ω)
      + (4 * ν) • setting.I (vsq ω * φ * wLapW setting ω)
      + setting.I (vsq ω * vsq ω * vsq ω) := by
  rw [← setting.int_dt, dt_weighted_div setting ν u ω φ hu hw hφ, map_sub, I_sum_d, sub_zero, map_add,
    map_add, map_smul, map_smul]

/-- `ω·(ω·∇)u` equals the stretching density, so (2) is the paper's form. -/
lemma stretch_eq (u ω : Fin 3 → A) : stretch setting u ω = ∑ i, ω i * adv setting ω (u i) := by
  simp only [stretch, adv, Finset.mul_sum]; refine sum_congr rfl fun i _ => sum_congr rfl ?_
  intro j _; ring

end WeightedEnstrophy
