module
public import MathCollab.Density.WeightedSquare

@[expose] public section

open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff

noncomputable section
namespace MathCollab.Density

def mellinMass (w : ReflectionCutoff) : ℝ := ∫ r, ‖mellinLine (fun x => (w x : ℂ)) r‖

def bandPhaseSum (L H v r : ℝ) : ℂ :=
  ∑ m ∈ reflectionBand L H, dirichletPhase ((m : ℝ)*L) (r-v)

theorem mellinMass_nonneg (w : ReflectionCutoff) : 0 ≤ mellinMass w :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem measurable_bandPhaseSum (L H v : ℝ) : Measurable (bandPhaseSum L H v) := by
  unfold bandPhaseSum dirichletPhase
  fun_prop

theorem norm_bandPhaseSum_le (L H v r : ℝ) :
    ‖bandPhaseSum L H v r‖ ≤ (reflectionBand L H).card := by
  exact (norm_sum_le _ _).trans_eq (by simp only [norm_dirichletPhase, Finset.sum_const,
    nsmul_eq_mul, mul_one])

/-- Interchange of the finite retained-mode sum with the full Mellin integral. -/
theorem bandContribution_mellin (w : ReflectionCutoff) {L H : ℝ}
    (hL : 0 < L) (hH : 0 < H) (v : ℝ) :
    bandContribution w L H v = ((L/(2*Real.pi) : ℝ) : ℂ) * ∫ r : ℝ,
      mellinLine (fun x => (w x : ℂ)) r *
        (reflectionKernel H v r * bandPhaseSum L H v r) := by
  rw [bandContribution, tsum_retainedMode_eq_finite]
  have he : (∑ m ∈ reflectionBand L H, modeIntegral (fun x => (w x : ℂ)) v ((m : ℝ)*L)) =
      ∑ m ∈ reflectionBand L H, ((1/(2*Real.pi) : ℝ) : ℂ) * ∫ r : ℝ,
        mellinLine (fun x => (w x : ℂ)) r * dirichletPhase ((m : ℝ)*L) (r-v) *
          reflectionKernel H v r := by
    apply Finset.sum_congr rfl
    intro m hm
    exact band_modeIntegral_mellin w.complex_smooth w.complex_support hL hH
      ((mem_reflectionBand L H m).1 hm) v
  rw [he]
  rw [← Finset.mul_sum]
  have hi := fun m (_ : m ∈ reflectionBand L H) =>
    integrable_reflection_kernel w.complex_smooth w.complex_support hH ((m : ℝ)*L) v
  rw [← integral_finsetSum _ hi]
  rw [← mul_assoc]
  have hc : (L : ℂ) * ((1/(2*Real.pi) : ℝ) : ℂ) = ((L/(2*Real.pi) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  simp only [bandPhaseSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Full-line weighted estimate for the retained band, uniform in the phase. -/
theorem norm_bandContribution_sq_le (w : ReflectionCutoff) {L H : ℝ}
    (hL : 0 < L) (hH : 0 < H) (v : ℝ) :
    ‖bandContribution w L H v‖ ^ 2 ≤
      (500 / Real.pi^2) * mellinMass w * (L^2/H) *
        ∫ r, ‖mellinLine (fun x => (w x : ℂ)) r‖ * ‖bandPhaseSum L H v r‖ ^ 2 := by
  let W := mellinLine (fun x => (w x : ℂ))
  let B := bandPhaseSum L H v
  let g := fun r => reflectionKernel H v r * B r
  have hW : Integrable W := integrable_mellin_line_one w.complex_smooth w.complex_support
  have hB : Measurable B := measurable_bandPhaseSum L H v
  have hg : Measurable g := (measurable_reflectionKernel hH v).mul hB
  have hk (r : ℝ) : ‖reflectionKernel H v r‖ ≤ Real.sqrt (2000/H) :=
    (Real.le_sqrt (norm_nonneg _) (by positivity)).2 (norm_reflectionKernel_sq_le hH v r)
  have hb (r : ℝ) : ‖B r‖ ≤ (reflectionBand L H).card := norm_bandPhaseSum_le L H v r
  have hgb (r : ℝ) : ‖g r‖ ≤ Real.sqrt (2000/H) * (reflectionBand L H).card := by
    rw [norm_mul]
    exact mul_le_mul (hk r) (hb r) (norm_nonneg _) (Real.sqrt_nonneg _)
  have hs := norm_integral_mul_sq_le hW hg.aestronglyMeasurable hgb
  have hiB := integrable_weighted_norm_sq hW hB.aestronglyMeasurable hb
  have hig := integrable_weighted_norm_sq hW hg.aestronglyMeasurable hgb
  have hp (r : ℝ) : ‖g r‖ ^ 2 ≤ (2000/H) * ‖B r‖ ^ 2 := by
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (norm_reflectionKernel_sq_le hH v r) (sq_nonneg _)
  have hint : (∫ r, ‖W r‖ * ‖g r‖ ^ 2) ≤
      (2000/H) * ∫ r, ‖W r‖ * ‖B r‖ ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae hig (hiB.const_mul (2000/H))
    filter_upwards with r
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left (hp r) (norm_nonneg (W r))
  have hs' : ‖∫ r, W r * g r‖ ^ 2 ≤
      mellinMass w * ((2000/H) * ∫ r, ‖W r‖ * ‖B r‖ ^ 2) :=
    hs.trans (mul_le_mul_of_nonneg_left hint (mellinMass_nonneg w))
  rw [bandContribution_mellin w hL hH, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (show 0 < L/(2*Real.pi) by positivity), mul_pow]
  calc
    _ ≤ (L/(2*Real.pi))^2 *
        (mellinMass w * ((2000/H) * ∫ r, ‖W r‖ * ‖B r‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hs' (sq_nonneg _)
    _ = _ := by dsimp [W, B]; ring

end MathCollab.Density
