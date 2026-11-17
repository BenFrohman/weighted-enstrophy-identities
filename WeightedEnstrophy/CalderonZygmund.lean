/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import WeightedEnstrophy.Lyapunov

/-!
# The `p = 2` case of `CalderonZygmundLp` on `T³`

Proved here, for genuine smooth `1`-periodic fields on `ℝ × T³` (the model `Smooth.A`):

* `gradU_sq_eq` (pointwise, any periodic differential setting with commuting `∂ₖ`):
  `Σᵢⱼ (∂ⱼuᵢ)² = |curl u|² + Σⱼ ∂ⱼ(Σᵢ uᵢ ∂ᵢuⱼ) − Σᵢ uᵢ ∂ᵢ(div u)`.
* `int_gradU_sq_eq` (abstract) and `int_gradU_sq_eq_smooth` (on `T³`): for `div u = 0` and
  `ω = curl u`, `∫_{T³} Σᵢⱼ (∂ⱼuᵢ)² = ∫_{T³} |ω|²`.
* `d_comm`: the spatial derivatives of `Smooth.A` commute (symmetry of the second derivative).
* `calderonZygmundLp_two : CalderonZygmundLp 2`, with constant `C = 1`: for every smooth
  periodic divergence-free `u` with `ω = curl u`, and every `t, i, j`,
  `∫_{T³} |∂ⱼuᵢ(t,·)|² ≤ ∫_{T³} |ω(t,·)|²`.
* `cz_hypotheses_nonvacuous`: the hypotheses of `CalderonZygmundLp` are met by a field with
  `∂₁u₀ ≠ 0` (`u = (sin 2πb, 0, 0)`), so the `p = 2` statement is not vacuous.

Not proved here: `CalderonZygmundLp p` for `p ≠ 2`. That is the `Lᵖ` boundedness of the
Riesz transforms on `T³` (Calderón–Zygmund theory), which Mathlib does not provide.
-/

open scoped ContDiff
open WeightedEnstrophy.Smooth WeightedEnstrophy.Torus WeightedEnstrophy.Lyapunov Finset

namespace WeightedEnstrophy

section Abstract

variable {K A B : Type*} [CommRing K] [CommRing A] [Algebra K A] [AddCommGroup B] [Module K B]
variable (S : PeriodicSetting K A B)

/-- `|∇u|² = Σᵢⱼ (∂ⱼuᵢ)²`. -/
def gradUSq (u : Fin 3 → A) : A := ∑ i, ∑ j, S.d j (u i) * S.d j (u i)

/-- **Pointwise identity.** If the spatial derivatives commute and `ω = curl u`
(`ωᵢ = ∂ᵢ₊₁uᵢ₊₂ − ∂ᵢ₊₂uᵢ₊₁`), then
`|∇u|² = |ω|² + Σⱼ ∂ⱼ(Σᵢ uᵢ ∂ᵢuⱼ) − Σᵢ uᵢ ∂ᵢ(div u)`. -/
theorem gradU_sq_eq (hcomm : ∀ i j f, S.d i (S.d j f) = S.d j (S.d i f)) (u w : Fin 3 → A)
    (hw : ∀ i, w i = S.d (i + 1) (u (i + 2)) - S.d (i + 2) (u (i + 1))) :
    gradUSq S u = vsq w + ∑ j, S.d j (∑ i, u i * S.d i (u j))
      - ∑ i, u i * S.d i (div S u) := by
  have h0 : w 0 = S.d 1 (u 2) - S.d 2 (u 1) := hw 0
  have h1 : w 1 = S.d 2 (u 0) - S.d 0 (u 2) := hw 1
  have h2 : w 2 = S.d 0 (u 1) - S.d 1 (u 0) := hw 2
  have c : ∀ i j, S.d j (S.d i (u j)) = S.d i (S.d j (u j)) := fun i j => hcomm j i (u j)
  simp only [gradUSq, vsq, div, Fin.sum_univ_three, map_add, Derivation.leibniz,
    smul_eq_mul, h0, h1, h2]
  linear_combination
    -(u 0 * c 0 0 + u 0 * c 0 1 + u 0 * c 0 2 + u 1 * c 1 0 + u 1 * c 1 1 + u 1 * c 1 2
      + u 2 * c 2 0 + u 2 * c 2 1 + u 2 * c 2 2)

/-- **`∫|∇u|² = ∫|ω|²`** for divergence-free `u` with `ω = curl u`, in any periodic setting
whose spatial derivatives commute. -/
theorem int_gradU_sq_eq (hcomm : ∀ i j f, S.d i (S.d j f) = S.d j (S.d i f))
    (u w : Fin 3 → A) (hu : div S u = 0)
    (hw : ∀ i, w i = S.d (i + 1) (u (i + 2)) - S.d (i + 2) (u (i + 1))) :
    S.I (gradUSq S u) = S.I (vsq w) := by
  rw [gradU_sq_eq S hcomm u w hw, hu, map_sub, map_add, I_sum_d]
  simp

end Abstract

namespace Smooth

/-- The spatial (indeed all) directional derivatives on `A` commute. -/
theorem D_comm (v w : E) (f : A) : D v (D w f) = D w (D v f) := by
  ext p
  simp only [D_apply]
  have hf := smooth f
  have hd : ∀ v' : E, ∀ q, fderiv ℝ (fun q => fderiv ℝ (f : E → ℝ) q v') q
      = (fderiv ℝ (fderiv ℝ (f : E → ℝ)) q).flip v' := by
    intro v' q
    have hc : DifferentiableAt ℝ (fderiv ℝ (f : E → ℝ)) q :=
      ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) q
    rw [fderiv_clm_apply hc (differentiableAt_const v'), fderiv_const_apply,
      ContinuousLinearMap.comp_zero, zero_add]
  show fderiv ℝ (fun q => fderiv ℝ (f : E → ℝ) q w) p v
    = fderiv ℝ (fun q => fderiv ℝ (f : E → ℝ) q v) p w
  rw [hd w p, hd v p]
  simp only [ContinuousLinearMap.flip_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt
    (by simpa using (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))).eq v w

theorem d_comm (i j : Fin 3) (f : A) : setting.d i (setting.d j f) = setting.d j (setting.d i f) :=
  D_comm (e i) (e j) f

/-- **`∫_{T³} |∇u|² = ∫_{T³} |ω|²`** for smooth periodic divergence-free `u`, `ω = curl u`. -/
theorem int_gradU_sq_eq_smooth (u w : Fin 3 → A) (hu : div setting u = 0)
    (hw : ∀ i, w i = setting.d (i + 1) (u (i + 2)) - setting.d (i + 2) (u (i + 1))) :
    I (gradUSq setting u) = I (vsq w) :=
  int_gradU_sq_eq setting d_comm u w hu hw

lemma coe_sum (s : Finset (Fin 3)) (f : Fin 3 → A) :
    ((∑ i ∈ s, f i : A) : E → ℝ) = ∑ i ∈ s, (f i : E → ℝ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma coe_vsq (w : Fin 3 → A) (x : E) :
    ((vsq w : A) : E → ℝ) x = ∑ i, (w i : E → ℝ) x ^ 2 := by
  simp [vsq, Finset.sum_apply, sq]

lemma coe_gradUSq (u : Fin 3 → A) (x : E) :
    ((gradUSq setting u : A) : E → ℝ) x = ∑ i, ∑ j, (setting.d j (u i) : E → ℝ) x ^ 2 := by
  simp [gradUSq, Finset.sum_apply, sq]

end Smooth

namespace Torus

/-- Monotonicity of the torus integral for continuous integrands. -/
theorem torusIntegral_mono {f g : E → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, f x ≤ g x) (t : ℝ) : torusIntegral f t ≤ torusIntegral g t := by
  unfold torusIntegral
  refine intervalIntegral.integral_mono_on zero_le_one
    ((cont_i2 hf).comp (Continuous.prodMk_right t) |>.intervalIntegrable 0 1)
    ((cont_i2 hg).comp (Continuous.prodMk_right t) |>.intervalIntegrable 0 1) fun a _ => ?_
  unfold i2
  refine intervalIntegral.integral_mono_on zero_le_one
    ((cont_i3 hf).comp (by fun_prop) |>.intervalIntegrable 0 1)
    ((cont_i3 hg).comp (by fun_prop) |>.intervalIntegrable 0 1) fun b _ => ?_
  unfold i3
  exact intervalIntegral.integral_mono_on zero_le_one
    (hf.comp (by fun_prop) |>.intervalIntegrable 0 1)
    (hg.comp (by fun_prop) |>.intervalIntegrable 0 1) fun c _ => h _

end Torus

namespace Lyapunov

/-- **`CalderonZygmundLp 2` holds, with constant `C = 1`.** For every smooth `1`-periodic
divergence-free velocity `u` on `ℝ × T³` with vorticity `ω = curl u`, and every `t, i, j`:
`∫_{T³} |∂ⱼuᵢ(t,·)|² ≤ ∫_{T³} |ω(t,·)|²`. This is the `p = 2` case of the open step
`CalderonZygmundLp p`; the cases `p ≠ 2` are not proved. -/
theorem calderonZygmundLp_two : CalderonZygmundLp 2 := by
  refine ⟨1, fun u w hu hw t i j => ?_⟩
  have hL : (fun x => |((setting.d j (u i) : A) : E → ℝ) x| ^ (2 : ℝ))
      = fun x => ((setting.d j (u i) : A) : E → ℝ) x ^ 2 := by
    funext x; rw [Real.rpow_two, sq_abs]
  have hR : (fun x => |((vsq w : A) : E → ℝ) x| ^ ((2 : ℝ) / 2))
      = ((vsq w : A) : E → ℝ) := by
    funext x
    rw [div_self two_ne_zero, Real.rpow_one, abs_of_nonneg]
    rw [coe_vsq]; positivity
  rw [hL, hR, one_mul]
  have key := congrFun (int_gradU_sq_eq_smooth u w hu hw) t
  change torusIntegral _ t = torusIntegral _ t at key
  rw [← key]
  apply torusIntegral_mono ((smooth _).continuous.pow 2) (smooth _).continuous
  intro x
  rw [coe_gradUSq]
  have hj : ((setting.d j (u i) : A) : E → ℝ) x ^ 2 ≤
      ∑ j', ((setting.d j' (u i) : A) : E → ℝ) x ^ 2 :=
    Finset.single_le_sum (f := fun j' => ((setting.d j' (u i) : A) : E → ℝ) x ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have hi : ∑ j', ((setting.d j' (u i) : A) : E → ℝ) x ^ 2 ≤
      ∑ i', ∑ j', ((setting.d j' (u i') : A) : E → ℝ) x ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ((setting.d j' (u i') : A) : E → ℝ) x ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact hj.trans hi

/-! ### Non-vacuity witness -/

/-- `sin (2π b)` as a smooth periodic field (`b` the second spatial coordinate). -/
noncomputable def sinB : A :=
  ⟨fun p => Real.sin (2 * Real.pi * p.2.2.1),
    ⟨Real.contDiff_sin.comp (contDiff_const.mul (by fun_prop)), fun k p => by
      fin_cases k <;> simp [e]
      rw [mul_add, mul_one, Real.sin_add_two_pi]⟩⟩

lemma sinB_line (p : E) (v : E) (x : ℝ) :
    HasDerivAt (fun s => Real.sin (2 * Real.pi * (p + s • v).2.2.1))
      (Real.cos (2 * Real.pi * (p + x • v).2.2.1) * (2 * Real.pi * v.2.2.1)) x := by
  have : HasDerivAt (fun s => 2 * Real.pi * (p + s • v).2.2.1) (2 * Real.pi * v.2.2.1) x := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_snd, Prod.smul_fst, smul_eq_mul]
    simpa using ((hasDerivAt_id x).mul_const v.2.2.1).const_add p.2.2.1 |>.const_mul (2 * Real.pi)
  exact (Real.hasDerivAt_sin _).comp x this

lemma fderiv_sinB (p v : E) :
    fderiv ℝ (sinB : E → ℝ) p v = Real.cos (2 * Real.pi * p.2.2.1) * (2 * Real.pi * v.2.2.1) := by
  have h1 := line_deriv' sinB p v 0 (fun s => p + s • v) (fun _ => rfl)
  have h2 := sinB_line p v 0
  simp only [zero_smul, add_zero] at h1 h2
  exact h1.unique h2

/-- **Non-vacuity.** The hypotheses of `CalderonZygmundLp` are satisfied by the smooth periodic
field `u = (sin 2πb, 0, 0)`, `ω = curl u`, which has `∂₁u₀ ≠ 0`. -/
theorem cz_hypotheses_nonvacuous :
    ∃ u w : Fin 3 → A, div setting u = 0 ∧
      (∀ i, w i = setting.d (i + 1) (u (i + 2)) - setting.d (i + 2) (u (i + 1))) ∧
      setting.d 1 (u 0) ≠ 0 := by
  let u : Fin 3 → A := ![sinB, 0, 0]
  refine ⟨u, fun i => setting.d (i + 1) (u (i + 2)) - setting.d (i + 2) (u (i + 1)),
    ?_, fun _ => rfl, ?_⟩
  · ext p
    simp only [div, Fin.sum_univ_three, u, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, map_zero, add_zero]
    show fderiv ℝ (sinB : E → ℝ) p (e 0) = 0
    rw [fderiv_sinB]; simp [e]
  · intro h
    have := congrArg (fun f : A => (f : E → ℝ) 0) h
    simp only [u, Matrix.cons_val_zero] at this
    change fderiv ℝ (sinB : E → ℝ) 0 (e 1) = ((0 : A) : E → ℝ) 0 at this
    rw [fderiv_sinB] at this
    simp [e, Real.pi_ne_zero] at this

end Lyapunov

end WeightedEnstrophy
