-- Axiom audit: prints the axioms of every theorem/lemma in the project.
-- CI fails unless each depends only on propext, Classical.choice, Quot.sound (or none).
import WeightedEnstrophy
import WeightedEnstrophy.Abstract
import WeightedEnstrophy.Fourier.Basic
import WeightedEnstrophy.Fourier.Strain
import WeightedEnstrophy.Lyapunov
import WeightedEnstrophy.Smooth
import WeightedEnstrophy.TorusCalculus
import WeightedEnstrophy.TrigModel

#print axioms WeightedEnstrophy.I_sum_d
#print axioms WeightedEnstrophy.PeriodicSetting.int_d
#print axioms WeightedEnstrophy.PeriodicSetting.int_dt
#print axioms WeightedEnstrophy.adv_eq
#print axioms WeightedEnstrophy.dt_half_sq
#print axioms WeightedEnstrophy.dt_vsq_div
#print axioms WeightedEnstrophy.dt_weighted
#print axioms WeightedEnstrophy.dt_weighted_div
#print axioms WeightedEnstrophy.enstrophy_identity
#print axioms WeightedEnstrophy.int_adv_eq_zero
#print axioms WeightedEnstrophy.stretch_eq
#print axioms WeightedEnstrophy.two_w_adv
#print axioms WeightedEnstrophy.wLapW_eq
#print axioms WeightedEnstrophy.weighted_identity
#print axioms WeightedEnstrophy.Fourier.coeff_eq_mFourierCoeff
#print axioms WeightedEnstrophy.Fourier.coeff_multiplier
#print axioms WeightedEnstrophy.Fourier.ext_coeff
#print axioms WeightedEnstrophy.Fourier.memℓp_mul
#print axioms WeightedEnstrophy.Fourier.norm_multiplier_le
#print axioms WeightedEnstrophy.Fourier.nsq_nonneg
#print axioms WeightedEnstrophy.Fourier.parseval_norm_sq
#print axioms WeightedEnstrophy.Fourier.summable_coeff_sq
#print axioms WeightedEnstrophy.Fourier.two_toReal
#print axioms WeightedEnstrophy.Fourier.L2_strain_eq
#print axioms WeightedEnstrophy.Fourier.L2_strain_le
#print axioms WeightedEnstrophy.Fourier.curl_deltaH_eq_u
#print axioms WeightedEnstrophy.Fourier.curl_sq_eq
#print axioms WeightedEnstrophy.Fourier.curl_stream_eq
#print axioms WeightedEnstrophy.Fourier.modeEnergy_curl
#print axioms WeightedEnstrophy.Fourier.modeEnergy_expand
#print axioms WeightedEnstrophy.Fourier.normsq_eq
#print axioms WeightedEnstrophy.Fourier.strain_sq_eq_half_curl_sq
#print axioms WeightedEnstrophy.Fourier.strain_sq_le_curl_sq
#print axioms WeightedEnstrophy.Lyapunov.dS_identity_smooth
#print axioms WeightedEnstrophy.Lyapunov.le_integral_sq_of_deriv
#print axioms WeightedEnstrophy.Lyapunov.ode_bounded
#print axioms WeightedEnstrophy.Lyapunov.ode_lower
#print axioms WeightedEnstrophy.Lyapunov.ode_upper
#print axioms WeightedEnstrophy.Smooth.D_apply
#print axioms WeightedEnstrophy.Smooth.enstrophy_identity_smooth
#print axioms WeightedEnstrophy.Smooth.fderiv_mem
#print axioms WeightedEnstrophy.Smooth.hasDerivAt_I
#print axioms WeightedEnstrophy.Smooth.int_d
#print axioms WeightedEnstrophy.Smooth.int_dt
#print axioms WeightedEnstrophy.Smooth.line_deriv'
#print axioms WeightedEnstrophy.Smooth.periodic
#print axioms WeightedEnstrophy.Smooth.smooth
#print axioms WeightedEnstrophy.Smooth.weighted_identity_smooth
#print axioms WeightedEnstrophy.Torus.cont_i2
#print axioms WeightedEnstrophy.Torus.cont_i3
#print axioms WeightedEnstrophy.Torus.cont_torusIntegral
#print axioms WeightedEnstrophy.Torus.hasDerivAt_integral01
#print axioms WeightedEnstrophy.Torus.hasDerivAt_torusIntegral
#print axioms WeightedEnstrophy.Torus.i2_add
#print axioms WeightedEnstrophy.Torus.i3_add
#print axioms WeightedEnstrophy.Torus.integral01_deriv_periodic
#print axioms WeightedEnstrophy.Torus.torusIntegral_add
#print axioms WeightedEnstrophy.Torus.torusIntegral_deriv_a
#print axioms WeightedEnstrophy.Torus.torusIntegral_deriv_b
#print axioms WeightedEnstrophy.Torus.torusIntegral_deriv_c
#print axioms WeightedEnstrophy.Torus.torusIntegral_smul
#print axioms WeightedEnstrophy.Trig.enstrophy_identity_T3
#print axioms WeightedEnstrophy.Trig.integral_dt
#print axioms WeightedEnstrophy.Trig.integral_dx
#print axioms WeightedEnstrophy.Trig.leibniz_of_singles
#print axioms WeightedEnstrophy.Trig.mapCoeff_apply
#print axioms WeightedEnstrophy.Trig.mapCoeff_single
#print axioms WeightedEnstrophy.Trig.mulSym_apply
#print axioms WeightedEnstrophy.Trig.mulSym_single
#print axioms WeightedEnstrophy.Trig.sym_add
#print axioms WeightedEnstrophy.Trig.sym_zero
#print axioms WeightedEnstrophy.Trig.weighted_identity_T3
