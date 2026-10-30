/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import WeightedEnstrophy.Abstract

/-!
# Trigonometric-polynomial model on `T³`

A field is a finite sum `Σₙ fₙ e^{2πi n·x}` over `n ∈ ℤ³`, with coefficients `fₙ` in a
commutative `ℂ`-algebra `R` carrying a derivation `D` (the time derivative of the
coefficients; e.g. `R` = time-dependent coefficients). Multiplication of fields is
`e^{2πi n·x} e^{2πi m·x} = e^{2πi (n+m)·x}`, i.e. `AddMonoidAlgebra R (Fin 3 → ℤ)`.
The spatial derivative `∂ₖ` multiplies mode `n` by `2πi nₖ`, the time derivative applies
`D` to every coefficient, and `∫_{T³}` (unit-volume torus) is the zero-mode coefficient.
-/

open Complex

namespace WeightedEnstrophy.Trig

variable {R : Type*} [CommRing R] [Algebra ℂ R]

/-- Fields on `T³`: trigonometric polynomials with coefficients in `R`. -/
abbrev Field (R : Type*) [CommRing R] := AddMonoidAlgebra R (Fin 3 → ℤ)

/-- Symbol of `∂ₖ` on the mode `e^{2πi n·x}`. -/
noncomputable def sym (k : Fin 3) (n : Fin 3 → ℤ) : ℂ := 2 * (Real.pi : ℂ) * I * (n k : ℂ)

lemma sym_add (k : Fin 3) (n m : Fin 3 → ℤ) : sym k (n + m) = sym k n + sym k m := by
  simp [sym]; ring

lemma sym_zero (k : Fin 3) : sym k 0 = 0 := by simp [sym]

/-- Multiply each coefficient by a mode-dependent scalar. -/
noncomputable def mulSym (c : (Fin 3 → ℤ) → ℂ) : Field R →ₗ[ℂ] Field R where
  toFun f := Finsupp.onFinset f.support (fun n => c n • f n) (by
    intro n hn; by_contra h; exact hn (by simp [Finsupp.notMem_support_iff.mp h]))
  map_add' f g := by ext n; simp [smul_add]
  map_smul' a f := by ext n; simp [smul_comm (c n) a]

@[simp] lemma mulSym_apply (c : (Fin 3 → ℤ) → ℂ) (f : Field R) (n) :
    mulSym c f n = c n • f n := by simp [mulSym]

lemma mulSym_single (c : (Fin 3 → ℤ) → ℂ) (n : Fin 3 → ℤ) (a : R) :
    mulSym c (AddMonoidAlgebra.single n a : Field R) = AddMonoidAlgebra.single n (c n • a) := by
  ext m; by_cases h : n = m
  · subst h; simp [AddMonoidAlgebra.single]
  · simp [AddMonoidAlgebra.single, h]

/-- Leibniz rule for a bilinear-in-singles check. -/
lemma leibniz_of_singles (L : Field R →ₗ[ℂ] Field R)
    (h : ∀ n m (a b : R), L (AddMonoidAlgebra.single n a * AddMonoidAlgebra.single m b) =
      AddMonoidAlgebra.single n a * L (AddMonoidAlgebra.single m b)
      + AddMonoidAlgebra.single m b * L (AddMonoidAlgebra.single n a)) (f g : Field R) :
    L (f * g) = f • L g + g • L f := by
  simp only [smul_eq_mul]
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂]; ring
  | single n a =>
    induction g using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add g₁ g₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]; ring
    | single m b => exact h n m a b

/-- The spatial derivation `∂ₖ` on `T³`. -/
noncomputable def dx (k : Fin 3) : Derivation ℂ (Field R) (Field R) :=
  Derivation.mk' (mulSym (sym k)) (leibniz_of_singles _ fun n m a b => by
    simp only [AddMonoidAlgebra.single_mul_single, mulSym_single, sym_add, add_smul]
    rw [mul_smul_comm, mul_smul_comm, add_comm m n, mul_comm b a, ← AddMonoidAlgebra.single_add,
      add_comm (sym k m • _)])

/-- Apply a coefficient map that vanishes at `0`. -/
noncomputable def mapCoeff (D : Derivation ℂ R R) : Field R →ₗ[ℂ] Field R where
  toFun f := Finsupp.onFinset f.support (fun n => D (f n)) (by
    intro n hn; by_contra h; exact hn (by simp [Finsupp.notMem_support_iff.mp h]))
  map_add' f g := by ext n; simp
  map_smul' a f := by ext n; simp

@[simp] lemma mapCoeff_apply (D : Derivation ℂ R R) (f : Field R) (n) :
    mapCoeff D f n = D (f n) := by simp [mapCoeff]

lemma mapCoeff_single (D : Derivation ℂ R R) (n : Fin 3 → ℤ) (a : R) :
    mapCoeff D (AddMonoidAlgebra.single n a : Field R) = AddMonoidAlgebra.single n (D a) := by
  ext m; by_cases h : n = m
  · subst h; simp [AddMonoidAlgebra.single]
  · simp [AddMonoidAlgebra.single, h]

/-- The time derivation: `D` applied to every Fourier coefficient. -/
noncomputable def dt (D : Derivation ℂ R R) : Derivation ℂ (Field R) (Field R) :=
  Derivation.mk' (mapCoeff D) (leibniz_of_singles _ fun n m a b => by
    simp only [AddMonoidAlgebra.single_mul_single, mapCoeff_single, Derivation.leibniz,
      smul_eq_mul]
    rw [add_comm m n, ← AddMonoidAlgebra.single_add])

/-- `∫_{T³} f dx` = zero-mode coefficient (unit-volume torus). -/
noncomputable def integral : Field R →ₗ[ℂ] R := Finsupp.lapply 0

/-- **Torus divergence lemma**: `∫_{T³} ∂ₖ f = 0` for every trigonometric polynomial. -/
theorem integral_dx (k : Fin 3) (f : Field R) : integral (dx (R := R) k f) = 0 := by
  show (mulSym (sym k) f) 0 = 0
  simp [sym_zero]

/-- `∫ ∂t f = D (∫ f)`. -/
theorem integral_dt (D : Derivation ℂ R R) (f : Field R) :
    integral (dt D f) = D (integral f) := by
  show (mapCoeff D f) 0 = D (f 0)
  simp

/-- The trigonometric-polynomial model is a periodic differential setting. -/
noncomputable def setting (D : Derivation ℂ R R) : PeriodicSetting ℂ (Field R) R where
  d := dx
  dt := dt D
  I := integral
  Dt := D
  int_d := integral_dx
  int_dt := integral_dt D

/-- **Identity (1) on trigonometric polynomials on `T³`.** -/
theorem enstrophy_identity_T3 (D : Derivation ℂ R R) (ν : ℂ) (u w : Fin 3 → Field R)
    (hu : div (setting D) u = 0) (hw : VorticityEq (setting D) ν u w) :
    D (integral (vsq w)) = (2 : ℂ) • integral (stretch (setting D) u w)
      - (2 * ν) • integral (gradSq (setting D) w) := by
  exact WeightedEnstrophy.enstrophy_identity (setting D) ν u w hu hw

/-- **Identity (2) on trigonometric polynomials on `T³`.** -/
theorem weighted_identity_T3 (D : Derivation ℂ R R) (ν : ℂ) (u w : Fin 3 → Field R)
    (φ : Field R) (hu : div (setting D) u = 0) (hw : VorticityEq (setting D) ν u w)
    (hφ : WeightEq (setting D) u w φ) :
    D (integral (vsq w * vsq w * φ)) =
      (4 : ℂ) • integral (vsq w * φ * stretch (setting D) u w)
      + (4 * ν) • integral (vsq w * φ * wLapW (setting D) w)
      + integral (vsq w * vsq w * vsq w) := by
  exact WeightedEnstrophy.weighted_identity (setting D) ν u w φ hu hw hφ

end WeightedEnstrophy.Trig
