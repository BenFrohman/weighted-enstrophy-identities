/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import WeightedEnstrophy.Abstract
import WeightedEnstrophy.TorusCalculus

/-!
# The smooth periodic model

`A` = real `C^∞` functions on `ℝ × ℝ³` (time `t`, space `(a,b,c)`) that are 1-periodic in each
spatial variable, i.e. smooth time-dependent fields on `T³ = (ℝ/ℤ)³`. Derivatives are Fréchet
directional derivatives; the integral is `∫_{T³} f(t,·)`, a function of `t`; `Dt = deriv`.
-/

open scoped ContDiff
open WeightedEnstrophy.Torus

namespace WeightedEnstrophy.Smooth

/-- Spatial unit vectors in `E = ℝ × ℝ × ℝ × ℝ`. -/
def e : Fin 3 → E
  | 0 => (0, 1, 0, 0)
  | 1 => (0, 0, 1, 0)
  | 2 => (0, 0, 0, 1)

/-- Time unit vector. -/
def eT : E := (1, 0, 0, 0)

/-- Smooth fields on `ℝ × T³`. -/
def A : Subalgebra ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ ∀ k p, f (p + e k) = f p}
  mul_mem' := fun {f g} hf hg => ⟨hf.1.mul hg.1, fun k p => by simp [hf.2 k p, hg.2 k p]⟩
  add_mem' := fun {f g} hf hg => ⟨hf.1.add hg.1, fun k p => by simp [hf.2 k p, hg.2 k p]⟩
  algebraMap_mem' := fun r => ⟨contDiff_const, fun _ _ => rfl⟩

lemma smooth (f : A) : ContDiff ℝ ∞ (f : E → ℝ) := f.2.1
lemma periodic (f : A) (k p) : (f : E → ℝ) (p + e k) = (f : E → ℝ) p := f.2.2 k p

lemma fderiv_mem (f : A) (v : E) : (fun p => fderiv ℝ (f : E → ℝ) p v) ∈ A := by
  refine ⟨((smooth f).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const, fun k p => ?_⟩
  have : (fun q => (f : E → ℝ) (q + e k)) = f := funext (periodic f k)
  show fderiv ℝ (f : E → ℝ) (p + e k) v = fderiv ℝ (f : E → ℝ) p v
  rw [← fderiv_comp_add_right, this]

/-- Directional derivative `∂_v` as a derivation of `A`. -/
noncomputable def D (v : E) : Derivation ℝ A A where
  toFun f := ⟨_, fderiv_mem f v⟩
  map_add' f g := by
    ext p; simp [fderiv_add ((smooth f).differentiable (by simp) p)
      ((smooth g).differentiable (by simp) p)]
  map_smul' r f := by
    ext p; simp [fderiv_const_smul ((smooth f).differentiable (by simp) p)]
  map_one_eq_zero' := by ext p; simp
  leibniz' f g := by
    ext p
    simp [fderiv_mul ((smooth f).differentiable (by simp) p)
      ((smooth g).differentiable (by simp) p)]

lemma D_apply (v : E) (f : A) (p : E) : (D v f : E → ℝ) p = fderiv ℝ (f : E → ℝ) p v := rfl

/-- The torus integral `f ↦ (t ↦ ∫_{T³} f(t,·))`. -/
noncomputable def I : A →ₗ[ℝ] (ℝ → ℝ) where
  toFun f := torusIntegral f
  map_add' f g := funext fun t =>
    torusIntegral_add (smooth f).continuous (smooth g).continuous t
  map_smul' r f := funext fun t => torusIntegral_smul r f t

lemma line_deriv' (f : A) (p v : E) (x : ℝ) (g : ℝ → E) (hg : ∀ s, g s = p + s • v) :
    HasDerivAt (fun s => (f : E → ℝ) (g s)) (fderiv ℝ (f : E → ℝ) (g x) v) x := by
  have hl : HasDerivAt g v x := by
    rw [show g = fun s => p + s • v from funext hg]
    simpa using ((hasDerivAt_id x).smul_const v).const_add p
  exact ((smooth f).differentiable (by simp) (g x)).hasFDerivAt.comp_hasDerivAt x hl

/-- **(a)** `∫_{T³} ∂ₖ f = 0`. -/
theorem int_d (k : Fin 3) (f : A) : I (D (e k) f) = 0 := by
  funext t
  have hc : Continuous (D (e k) f : E → ℝ) := (smooth (D (e k) f)).continuous
  show torusIntegral _ t = 0
  fin_cases k
  · exact torusIntegral_deriv_a (smooth f).continuous hc
      (fun t a b c => line_deriv' f (t, 0, b, c) _ a _ (fun s => by simp [e]))
      (fun t a b c => by simpa [e] using periodic f 0 (t, a, b, c)) t
  · exact torusIntegral_deriv_b (smooth f).continuous hc
      (fun t a b c => line_deriv' f (t, a, 0, c) _ b _ (fun s => by simp [e]))
      (fun t a b c => by simpa [e] using periodic f 1 (t, a, b, c)) t
  · exact torusIntegral_deriv_c hc
      (fun t a b c => line_deriv' f (t, a, b, 0) _ c _ (fun s => by simp [e]))
      (fun t a b c => by simpa [e] using periodic f 2 (t, a, b, c)) t

/-- **(b)** `d/dt ∫_{T³} f = ∫_{T³} ∂ₜ f` (differentiation under the integral sign). -/
theorem hasDerivAt_I (f : A) (t : ℝ) : HasDerivAt (I f) (I (D eT f) t) t :=
  hasDerivAt_torusIntegral (smooth f).continuous (smooth (D eT f)).continuous
    (fun t a b c => line_deriv' f (0, a, b, c) _ t _ (fun s => by simp [eT])) t

theorem int_dt (f : A) : I (D eT f) = deriv (I f) :=
  funext fun t => (hasDerivAt_I f t).deriv.symm

/-- The smooth periodic model is a `PeriodicSetting`. -/
noncomputable def setting : PeriodicSetting ℝ A (ℝ → ℝ) where
  d k := D (e k)
  dt := D eT
  I := I
  Dt := deriv
  int_d := int_d
  int_dt := int_dt

/-- **Identity (1)** for smooth periodic fields:
`d/dt ∫|ω|² = 2∫ ωᵢωⱼ∂ⱼuᵢ − 2ν ∫|∇ω|²`, given `div u = 0` and the vorticity equation. -/
theorem enstrophy_identity_smooth (ν : ℝ) (u w : Fin 3 → A)
    (hu : div setting u = 0) (hw : VorticityEq setting ν u w) :
    deriv (I (vsq w)) = (2 : ℝ) • I (stretch setting u w) - (2 * ν) • I (gradSq setting w) :=
  WeightedEnstrophy.enstrophy_identity setting ν u w hu hw

/-- **Identity (2)** for smooth periodic fields, given `div u = 0`, the vorticity equation and
the weight equation `∂ₜφ + u·∇φ = |ω|²`. -/
theorem weighted_identity_smooth (ν : ℝ) (u w : Fin 3 → A) (φ : A)
    (hu : div setting u = 0) (hw : VorticityEq setting ν u w) (hφ : WeightEq setting u w φ) :
    deriv (I (vsq w * vsq w * φ)) =
      (4 : ℝ) • I (vsq w * φ * stretch setting u w)
      + (4 * ν) • I (vsq w * φ * wLapW setting w)
      + I (vsq w * vsq w * vsq w) :=
  WeightedEnstrophy.weighted_identity setting ν u w φ hu hw hφ

end WeightedEnstrophy.Smooth
