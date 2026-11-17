/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import WeightedEnstrophy.Smooth

/-!
# The functional `½‖ω‖²_{L²} − (κ/2)∫|ω|⁴φ`, the comparison ODE, and the open steps

Proved here:
* `dS_identity_smooth`: exact formula for `d/dt (½‖ω‖²_{L²} − (κ/2)∫|ω|⁴φ)` for smooth periodic solutions.
* `le_integral_sq_of_deriv`: `g(t) ≤ ∫₀ᵗ ‖ω(s)‖²_{L∞} ds` when `g(0)=0`, `g'(s) ≤ ‖ω(s)‖²_{L∞}` (the weight along a path).
* `ode_bounded`: solutions of `y' = y²(C − κy)` (`κ > 0`) stay in `[min y₀ 0, max y₀ (max (C/κ) 0)]`.

Stated as `Prop`s and **not** proved here (the paper's corresponding steps are not established):
`CalderonZygmundLp` (its `p = 2` case is proved in `WeightedEnstrophy/CalderonZygmund.lean`),
`WeightedToSupReduction`, `PhiSupControl`.
-/

open WeightedEnstrophy.Smooth WeightedEnstrophy.Torus Set

namespace WeightedEnstrophy.Lyapunov

/-- The enstrophy `‖ω(t)‖²_{L²(𝕋³)} = ∫_{𝕋³} |ω(t,x)|² dx`. -/
noncomputable def enstrophy (ω : Fin 3 → A) (t : ℝ) : ℝ := I (vsq ω) t
/-- The functional `½‖ω(t)‖²_{L²(𝕋³)} − (κ/2) ∫_{𝕋³} |ω(t,x)|⁴ φ(t,x) dx`. -/
noncomputable def lyapunovFunctional (κ : ℝ) (ω : Fin 3 → A) (φ : A) (t : ℝ) : ℝ :=
  (1 / 2) * enstrophy ω t - κ / 2 * I (vsq ω * vsq ω * φ) t

/-- **Exact evolution of `½‖ω‖²_{L²} − (κ/2)∫|ω|⁴φ`** for smooth periodic solutions (`div u = 0`, vorticity equation,
weight equation):
`d/dt (½‖ω‖²_{L²} − (κ/2)∫|ω|⁴φ) = ∫ωᵢωⱼ∂ⱼuᵢ − ν‖∇ω‖²_{L²} − (κ/2)(4∫|ω|²φ ωᵢωⱼ∂ⱼuᵢ + 4ν∫|ω|²φ ω·Δω + ∫|ω|⁶)`. -/
theorem dS_identity_smooth (κ ν : ℝ) (u ω : Fin 3 → A) (φ : A)
    (hu : div setting u = 0) (hw : VorticityEq setting ν u ω) (hφ : WeightEq setting u ω φ)
    (t : ℝ) :
    HasDerivAt (lyapunovFunctional κ ω φ)
      (I (stretch setting u ω) t - ν * I (gradSq setting ω) t
        - κ / 2 * (4 * I (vsq ω * φ * stretch setting u ω) t
          + 4 * ν * I (vsq ω * φ * wLapW setting ω) t + I (vsq ω * vsq ω * vsq ω) t)) t := by
  have h1 := hasDerivAt_I (vsq ω) t
  have h2 := hasDerivAt_I (vsq ω * vsq ω * φ) t
  have e1 := congrFun (enstrophy_identity_smooth ν u ω hu hw) t
  have e2 := congrFun (weighted_identity_smooth ν u ω φ hu hw hφ) t
  rw [h1.deriv] at e1; rw [h2.deriv] at e2
  have := (h1.const_mul (1 / 2)).sub (h2.const_mul (κ / 2))
  convert this using 1
  rw [e1, e2]; simp [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]; ring

/-- **Weight along a path.** If `g(0) = 0` and `g'(s) = h(s) ≤ ‖ω(s)‖²_{L∞}` on `[0,t]`
(e.g. `g(s) = φ(s, X(s))` along a particle path, where `g' = |ω|²(s,X(s))`), then
`g(t) ≤ ∫₀ᵗ ‖ω(s)‖²_{L∞} ds`. The argument `vorticityLinfNorm` is the function
`s ↦ ‖ω(s)‖_{L∞(𝕋³)}`; the lemma is proved for every continuous real function in that slot. -/
theorem le_integral_sq_of_deriv (g h vorticityLinfNorm : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hg : ∀ s ∈ Icc 0 t, HasDerivAt g (h s) s) (hh : Continuous h) (hM : Continuous vorticityLinfNorm)
    (hle : ∀ s ∈ Icc 0 t, h s ≤ vorticityLinfNorm s ^ 2) (h0 : g 0 = 0) :
    g t ≤ ∫ s in (0:ℝ)..t, vorticityLinfNorm s ^ 2 := by
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
`∫|∂ⱼuᵢ|^p ≤ C ∫|ω|^p` for divergence-free `u` with `ω = curl u`. (True classical theorem.
Only `p = 2` is formalized: `calderonZygmundLp_two` in `WeightedEnstrophy/CalderonZygmund.lean`.
The `L∞` version used in the paper is false and is not stated.) -/
def CalderonZygmundLp (p : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (u ω : Fin 3 → A), div setting u = 0 →
    (∀ i, ω i = setting.d (i + 1) (u (i + 2)) - setting.d (i + 2) (u (i + 1))) →
    ∀ t i j, torusIntegral (fun x => |(setting.d j (u i) : SpaceTime → ℝ) x| ^ p) t ≤
      C * torusIntegral (fun x => (|((vsq ω : A) : SpaceTime → ℝ) x|) ^ (p / 2)) t

/-- The reduction the paper's Section 5 needs: a bound on `½‖ω(t)‖²_{L²} − (κ/2)∫|ω|⁴φ` on
`[0,T)` forces a bound on `‖ω(t)‖²_{L∞} = sup_x |ω(t,x)|²` on the same horizon, with a constant `B'` that may depend on `T`.
No bound uniform in `T` is asked for. Not proved. -/
def WeightedToSupReduction (κ ν : ℝ) : Prop :=
  ∀ (u ω : Fin 3 → A) (φ : A) (T B : ℝ), div setting u = 0 → VorticityEq setting ν u ω →
    WeightEq setting u ω φ → (∀ t ∈ Ico 0 T, lyapunovFunctional κ ω φ t ≤ B) →
    ∃ B' : ℝ, ∀ t ∈ Ico 0 T, ∀ x : ℝ × ℝ × ℝ, ((vsq ω : A) : SpaceTime → ℝ) (t, x) ≤ B'

/-- Finite-horizon control of `‖φ(t)‖∞` (Section 6): for each horizon `T` there is a bound `B`,
which may depend on `T` and on the solution, with `|φ| ≤ B` on `[0,T)`. No bound uniform in `T`
is asked for. Not proved. -/
def PhiSupControl (ν : ℝ) : Prop :=
  ∀ (u ω : Fin 3 → A) (φ : A) (T : ℝ), div setting u = 0 → VorticityEq setting ν u ω →
    WeightEq setting u ω φ → ∃ B : ℝ, ∀ t ∈ Ico 0 T, ∀ x : ℝ × ℝ × ℝ, |(φ : SpaceTime → ℝ) (t, x)| ≤ B

end WeightedEnstrophy.Lyapunov
