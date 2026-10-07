module
public import MathCollab.Density.ReflectionDefinitions
public import MathCollab.Density.AnalyticTransforms

@[expose] public section

open Real Complex Set MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap ContDiff

noncomputable section
namespace MathCollab.Density

/-- Smooth, compactly supported extension of the positive logarithmic modulation. -/
def logCutoff (w : ℝ → ℂ) (v x : ℝ) : ℂ := w x * dirichletPhase x v

theorem compactSupport_of_cutoff_support {w : ℝ → ℂ}
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) : HasCompactSupport w :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport w) hws

theorem logCutoff_hasCompactSupport {w : ℝ → ℂ}
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) (v : ℝ) :
    HasCompactSupport (logCutoff w v) :=
  (compactSupport_of_cutoff_support hws).mul_right

theorem logCutoff_contDiff {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) (v : ℝ) :
    ContDiff ℝ ∞ (logCutoff w v) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_const.congr_of_eventuallyEq (f := fun _ : ℝ => (0 : ℂ))
    filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
    have hnot : y ∉ tsupport w := fun hh => (not_le.mpr hy) (hws hh).1
    simp only [logCutoff, image_eq_zero_of_notMem_tsupport hnot, zero_mul]
  · unfold logCutoff dirichletPhase
    apply hw.contDiffAt.mul
    apply Complex.contDiff_exp.contDiffAt.comp
    exact contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (contDiffAt_const.mul (Real.contDiffAt_log.mpr hx)))

theorem fourier_logCutoff (w : ℝ → ℂ)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) (v k : ℝ) :
    FourierTransform.fourier (logCutoff w v) k = modeIntegral w v k := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold modeIntegral
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
    have hn : x ∉ tsupport w := by
      intro hh
      have hpos := (hws hh).1
      apply hx
      change 0 < x
      linarith
    simp only [image_eq_zero_of_notMem_tsupport hn, zero_mul])]
  apply integral_congr_ae
  filter_upwards with x
  simp only [logCutoff, dirichletPhase, smul_eq_mul]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Scaled Poisson specialized to the manuscript's logarithmic phase. -/
theorem scaled_log_poisson {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) {L : ℝ} (hL : 0 < L) (v : ℝ) :
    (∑' n : ℤ, w ((n : ℝ) / L) * dirichletPhase ((n : ℝ) / L) v) =
      (L : ℂ) * ∑' m : ℤ, modeIntegral w v ((m : ℝ) * L) := by
  have hh := Transforms.scaled_modulated_poisson (logCutoff w v)
    (logCutoff_hasCompactSupport hws v) (logCutoff_contDiff hw hws v) (inv_pos.mpr hL) 0
  simpa only [Transforms.sourcePhase, zero_mul, mul_zero, Complex.ofReal_zero, Complex.exp_zero,
    mul_one, sub_zero, inv_inv, div_inv_eq_mul, smul_eq_mul, Complex.real_smul,
    logCutoff, div_eq_mul_inv, mul_comm (L⁻¹), fourier_logCutoff w hws] using hh

/-- Absolute integrability of the full Mellin line, without a Mellin-frequency cutoff. -/
theorem integrable_mellin_line_one {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) :
    Integrable (fun r : ℝ => mellin w ((1 : ℂ) + r * Complex.I)) := by
  have hs : ∀ x, x ∉ Icc (1 / 2 : ℝ) 5 → w x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport (fun hh => hx (hws hh))
  let psi : 𝓢(ℝ, ℂ) := Transforms.mellinLogLiftSchwartz w
    (Transforms.mellinLogLift_hasCompactSupport (by norm_num) (by norm_num) hs)
    (Transforms.mellinLogLift_contDiff hw)
  have hh := (𝓕 psi : 𝓢(ℝ, ℂ)).integrable.comp_div (by positivity : 2 * Real.pi ≠ 0)
  convert hh using 1
  funext r
  exact Transforms.mellin_line_one_eq_fourier_logLift w r

/-- Mellin inversion with convergence and vertical integrability discharged. -/
theorem cutoff_mellin_inversion {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) {x : ℝ} (hx : 0 < x) :
    w x = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ r : ℝ,
      (x : ℂ) ^ (-((1 : ℂ) + r * Complex.I)) * mellin w ((1 : ℂ) + r * Complex.I) := by
  apply Transforms.mellin_inversion_line_one w hx
  · exact Transforms.mellinConvergent_one_of_compactSupport hw.continuous
      (compactSupport_of_cutoff_support hws)
  · exact integrable_mellin_line_one hw hws
  · exact hw.continuous.continuousAt

theorem summable_modeIntegral {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) {L : ℝ} (hL : 0 < L) (v : ℝ) :
    Summable (fun m : ℤ => modeIntegral w v ((m : ℝ) * L)) := by
  let psi : 𝓢(ℝ, ℂ) := (logCutoff_hasCompactSupport hws v).toSchwartzMap
    (logCutoff_contDiff hw hws v)
  let g : 𝓢(ℝ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL.ne')) (𝓕 psi)
  have hh : Summable (fun m : ℤ => g (m : ℝ)) := summable_of_isBigO
    (Real.summable_abs_int_rpow (by norm_num : (1 : ℝ) < 2))
    ((g.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  convert hh using 1
  funext m
  exact (fourier_logCutoff w hws v ((m : ℝ) * L)).symm

theorem summable_nat_logCutoff {w : ℝ → ℂ}
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) {L : ℝ} (hL : 0 < L) (v : ℝ) :
    Summable (fun n : ℕ => logCutoff w v ((n : ℝ) / L)) := by
  apply summable_of_ne_finset_zero (s := Finset.range (⌈5 * L⌉₊ + 1))
  intro n hn
  have hn' : ⌈5 * L⌉₊ < n := by simpa using hn
  have hbig : 5 < (n : ℝ) / L := (lt_div_iff₀ hL).2 (Nat.lt_of_ceil_lt hn')
  have hnot : (n : ℝ) / L ∉ tsupport w := fun hh => (not_le.mpr hbig) (hws hh).2
  simp only [logCutoff, image_eq_zero_of_notMem_tsupport hnot, zero_mul]

set_option maxHeartbeats 800000 in
theorem tsum_int_logCutoff_eq_nat {w : ℝ → ℂ}
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) {L : ℝ} (hL : 0 < L) (v : ℝ) :
    (∑' n : ℤ, logCutoff w v ((n : ℝ) / L)) =
      ∑' n : ℕ, logCutoff w v ((n : ℝ) / L) := by
  have hz (n : ℕ) : logCutoff w v (((-((n : ℤ) + 1) : ℤ) : ℝ) / L) = 0 := by
    have hx : (((-((n : ℤ) + 1) : ℤ) : ℝ) / L) < 1 / 2 := by
      apply (div_lt_iff₀ hL).2
      push_cast
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hnot : (((-((n : ℤ) + 1) : ℤ) : ℝ) / L) ∉ tsupport w :=
      fun hh => (not_le.mpr hx) (hws hh).1
    simp only [logCutoff, image_eq_zero_of_notMem_tsupport hnot, zero_mul]
  have hn : Summable (fun n : ℕ => logCutoff w v (((-((n : ℤ) + 1) : ℤ) : ℝ) / L)) := by
    simp only [hz, summable_zero]
  have hh := tsum_of_nat_of_neg_add_one (f := fun n : ℤ => logCutoff w v ((n : ℝ) / L))
    (summable_nat_logCutoff hws hL v) hn
  simpa only [Int.cast_natCast, hz, tsum_zero, add_zero] using hh

/-- Exact removal of the zero Fourier mode; both signs of integer modes remain. -/
theorem poisson_nonzero_modes {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) {L : ℝ} (hL : 0 < L) (v : ℝ) :
    (∑' n : ℕ, w ((n : ℝ) / L) * dirichletPhase ((n : ℝ) / L) v) -
        (L : ℂ) * modeIntegral w v 0 =
      (L : ℂ) * ∑' m : ℤ, nonzeroMode w L v m := by
  have hp := scaled_log_poisson hw hws hL v
  have hn := tsum_int_logCutoff_eq_nat hws hL v
  unfold logCutoff at hn
  change (∑' n : ℤ, w ((n : ℝ) / L) * dirichletPhase ((n : ℝ) / L) v) = _ at hn
  rw [← hn, hp]
  have hh := (summable_modeIntegral hw hws hL v).tsum_eq_add_tsum_ite 0
  simp only [Int.cast_zero, zero_mul] at hh
  rw [hh]
  simp only [nonzeroMode, mul_add, add_sub_cancel_left]

theorem ReflectionCutoff.complex_smooth (w : ReflectionCutoff) :
    ContDiff ℝ ∞ (fun x : ℝ => (w x : ℂ)) := by
  exact Complex.ofRealCLM.contDiff.comp w.smooth

theorem ReflectionCutoff.complex_support (w : ReflectionCutoff) :
    tsupport (fun x : ℝ => (w x : ℂ)) ⊆ Icc (1 / 2 : ℝ) 5 :=
  (tsupport_comp_subset (g := fun x : ℝ => (x : ℂ)) rfl w.toFun).trans w.support

theorem modeIntegral_zero_frequency (w : ReflectionCutoff) (v : ℝ) :
    modeIntegral (fun x => (w x : ℂ)) v 0 = cutoffIntegral w v := by
  unfold modeIntegral cutoffIntegral dirichletPhase
  simp only [mul_zero, zero_mul, sub_zero, mul_comm Complex.I]

/-- Exact Poisson formula for the manuscript kernel. -/
theorem hKernel_poisson (w : ReflectionCutoff) {L : ℝ} (hL : 0 < L) (v : ℝ) :
    hKernel w L v = (L : ℂ) * ∑' m : ℤ, nonzeroMode (fun x => (w x : ℂ)) L v m := by
  simpa only [modeIntegral_zero_frequency, hKernel] using
    poisson_nonzero_modes w.complex_smooth w.complex_support hL v

end MathCollab.Density
