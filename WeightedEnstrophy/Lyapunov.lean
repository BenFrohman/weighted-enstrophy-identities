/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import WeightedEnstrophy.Smooth

/-!
# The functional `S = E − (κ/2) Q`, the comparison ODE, and the open steps

Proved here:
* `dS_identity_smooth`: exact formula for `dS/dt` for smooth periodic solutions.
* `le_integral_sq_of_deriv`: `g(t) ≤ ∫₀ᵗ M²` when `g(0)=0`, `g' ≤ M²` (the weight along a path).
* `ode_bounded`: solutions of `y' = y²(C − κy)` (`κ > 0`) stay in `[min y₀ 0, max y₀ (max (C/κ) 0)]`.

Stated as `Prop`s and **not** proved (the paper's corresponding steps are not established):
`CalderonZygmundLp`, `WeightedToSupReduction`, `PhiSupControl`.
-/

open WeightedEnstrophy.Smooth WeightedEnstrophy.Torus Set

namespace WeightedEnstrophy.Lyapunov

/-- `E(t) = ½ ∫|ω|²`. -/
noncomputable def En (w : Fin 3 → A) (t : ℝ) : ℝ := (1 / 2) * I (vsq w) t
/-- `Q(t) = ∫ |ω|⁴ φ`. -/
noncomputable def Q (w : Fin 3 → A) (φ : A) (t : ℝ) : ℝ := I (vsq w * vsq w * φ) t
/-- `S(t) = E(t) − (κ/2) Q(t)`. -/
noncomputable def S (κ : ℝ) (w : Fin 3 → A) (φ : A) (t : ℝ) : ℝ := En w t - κ / 2 * Q w φ t

/-- **Exact evolution of `S`** for smooth periodic solutions (`div u = 0`, vorticity equation,
weight equation):
`S' = ∫ωᵢωⱼ∂ⱼuᵢ − ν∫|∇ω|² − (κ/2)(4∫|ω|²φ ωᵢωⱼ∂ⱼuᵢ + 4ν∫|ω|²φ ω·Δω + ∫|ω|⁶)`. -/
theorem dS_identity_smooth (κ ν : ℝ) (u w : Fin 3 → A) (φ : A)
    (hu : div setting u = 0) (hw : VorticityEq setting ν u w) (hφ : WeightEq setting u w φ)
    (t : ℝ) :
    HasDerivAt (S κ w φ)
      (I (stretch setting u w) t - ν * I (gradSq setting w) t
        - κ / 2 * (4 * I (vsq w * φ * stretch setting u w) t
          + 4 * ν * I (vsq w * φ * wLapW setting w) t + I (vsq w * vsq w * vsq w) t)) t := by
  have h1 := hasDerivAt_I (vsq w) t
  have h2 := hasDerivAt_I (vsq w * vsq w * φ) t
  have e1 := congrFun (enstrophy_identity_smooth ν u w hu hw) t
  have e2 := congrFun (weighted_identity_smooth ν u w φ hu hw hφ) t
  rw [h1.deriv] at e1; rw [h2.deriv] at e2
  have := (h1.const_mul (1 / 2)).sub (h2.const_mul (κ / 2))
  convert this using 1
  rw [e1, e2]; simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]; ring

/-- **Weight along a path.** If `g(0) = 0` and `g'(s) = h(s) ≤ M(s)²` on `[0,t]`
(e.g. `g(s) = φ(s, X(s))` along a particle path, where `g' = |ω|²(s,X(s))`), then
`g(t) ≤ ∫₀ᵗ M(s)² ds`. -/
theorem le_integral_sq_of_deriv (g h M : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hg : ∀ s ∈ Icc 0 t, HasDerivAt g (h s) s) (hh : Continuous h) (hM : Continuous M)
    (hle : ∀ s ∈ Icc 0 t, h s ≤ M s ^ 2) (h0 : g 0 = 0) :
    g t ≤ ∫ s in (0:ℝ)..t, M s ^ 2 := by
  have : ∫ s in (0:ℝ)..t, h s = g t - g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hg s (by
      rwa [uIcc_of_le ht] at hs)) (hh.intervalIntegrable 0 t)
  rw [h0, sub_zero] at this
  rw [← this]
  exact intervalIntegral.integral_mono_on ht (hh.intervalIntegrable 0 t)
    ((hM.pow 2).intervalIntegrable 0 t) hle

/-- Upper barrier for `y' = y²(C − κy)`. -/
theorem ode_upper (C κ : ℝ) (hκ : 0 < κ) (y : ℝ → ℝ) (T : ℝ)
    (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (y t ^ 2 * (C - κ * y t)) t) :
    ∀ t ∈ Icc 0 T, y t ≤ max (y 0) (max (C / κ) 0) := by
  set B := max (y 0) (max (C / κ) 0)
  intro t ht
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hcont : ContinuousOn y (Icc 0 T) := fun s hs => (hy s hs).continuousAt.continuousWithinAt
  have key := image_le_of_deriv_right_lt_deriv_boundary' (a := 0) (b := T) (f := y)
    (f' := fun s => y s ^ 2 * (C - κ * y s)) hcont
    (fun s hs => (hy s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (B := fun _ => B + ε) (B' := fun _ => 0) (by simp [B]; linarith [le_max_left (y 0) (max (C/κ) 0)])
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _) ?_ ht
  · linarith [key]
  · intro s _ hs
    have hB0 : 0 ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
    have hBC : C / κ ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
    have hpos : 0 < y s := by rw [hs]; linarith
    have hneg : C - κ * y s < 0 := by
      rw [hs]; have := (div_le_iff₀ hκ).1 hBC; nlinarith
    have : 0 < y s ^ 2 := by positivity
    simp only; nlinarith

/-- Lower barrier for `y' = y²(C − κy)`. -/
theorem ode_lower (C κ : ℝ) (hκ : 0 < κ) (y : ℝ → ℝ) (T : ℝ)
    (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (y t ^ 2 * (C - κ * y t)) t) :
    ∀ t ∈ Icc 0 T, min (y 0) (min (C / κ) 0) ≤ y t := by
  set m := min (y 0) (min (C / κ) 0)
  intro t ht
  have hy' : ∀ s ∈ Icc 0 T, HasDerivAt (fun s => -y s) (-(y s ^ 2 * (C - κ * y s))) s :=
    fun s hs => (hy s hs).neg
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hcont : ContinuousOn (fun s => -y s) (Icc 0 T) :=
    fun s hs => (hy' s hs).continuousAt.continuousWithinAt
  have key := image_le_of_deriv_right_lt_deriv_boundary' (a := 0) (b := T) (f := fun s => -y s)
    (f' := fun s => -(y s ^ 2 * (C - κ * y s))) hcont
    (fun s hs => (hy' s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (B := fun _ => -m + ε) (B' := fun _ => 0)
      (by simp only; linarith [min_le_left (y 0) (min (C/κ) 0)])
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _) ?_ ht
  · simp only at key; linarith [key]
  · intro s _ hs
    simp only at hs ⊢
    have hm0 : m ≤ 0 := le_trans (min_le_right _ _) (min_le_right _ _)
    have hmC : m ≤ C / κ := le_trans (min_le_right _ _) (min_le_left _ _)
    have hys : y s = m - ε := by linarith
    have hneg : y s < 0 := by linarith
    have hpos : 0 < C - κ * y s := by
      have := (le_div_iff₀ hκ).1 hmC; nlinarith
    have : 0 < y s ^ 2 := by nlinarith
    nlinarith

/-- **Section 7, proved unconditionally.** Every solution of `y' = y²(C − κy)` with `κ > 0`
on `[0,T]` is bounded by constants depending only on `y(0)`, `C`, `κ` (not on `T`). -/
theorem ode_bounded (C κ : ℝ) (hκ : 0 < κ) (y : ℝ → ℝ) (T : ℝ)
    (hy : ∀ t ∈ Icc 0 T, HasDerivAt y (y t ^ 2 * (C - κ * y t)) t) :
    ∀ t ∈ Icc 0 T, min (y 0) (min (C / κ) 0) ≤ y t ∧ y t ≤ max (y 0) (max (C / κ) 0) :=
  fun t ht => ⟨ode_lower C κ hκ y T hy t ht, ode_upper C κ hκ y T hy t ht⟩

/-! ### Open steps, stated as hypotheses only (not proved, not assumed anywhere above) -/

/-- `L^p` Calderón–Zygmund bound on `T³` for `1 < p < ∞`:
`∫|∂ⱼuᵢ|^p ≤ C ∫|ω|^p` for divergence-free `u` with `ω = curl u`. (True classical theorem;
not formalized here. The `L∞` version used in the paper is false and is not stated.) -/
def CalderonZygmundLp (p : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (u w : Fin 3 → A), div setting u = 0 →
    (∀ i, w i = setting.d (i + 1) (u (i + 2)) - setting.d (i + 2) (u (i + 1))) →
    ∀ t i j, torusIntegral (fun x => |(setting.d j (u i) : E → ℝ) x| ^ p) t ≤
      C * torusIntegral (fun x => (|((vsq w : A) : E → ℝ) x|) ^ (p / 2)) t

/-- The reduction the paper's Section 5 needs: a bound on `S` on `[0,T)` forces a bound on
`M(t)² = sup |ω(t,·)|²`. Not proved. -/
def WeightedToSupReduction (κ ν : ℝ) : Prop :=
  ∀ (u w : Fin 3 → A) (φ : A) (T B : ℝ), div setting u = 0 → VorticityEq setting ν u w →
    WeightEq setting u w φ → (∀ t ∈ Ico 0 T, S κ w φ t ≤ B) →
    ∃ B' : ℝ, ∀ t ∈ Ico 0 T, ∀ x : ℝ × ℝ × ℝ, ((vsq w : A) : E → ℝ) (t, x) ≤ B'

/-- Uniform control of `‖φ(t)‖∞` on `[0,T)` (Section 6). Not proved. -/
def PhiSupControl (ν : ℝ) : Prop :=
  ∀ (u w : Fin 3 → A) (φ : A) (T : ℝ), div setting u = 0 → VorticityEq setting ν u w →
    WeightEq setting u w φ → ∃ B : ℝ, ∀ t ∈ Ico 0 T, ∀ x : ℝ × ℝ × ℝ, |(φ : E → ℝ) (t, x)| ≤ B

end WeightedEnstrophy.Lyapunov
