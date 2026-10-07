module
public import MathCollab.Density.DetectorError

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The original summand, with the n=0 coefficient equal to zero. -/
def detectorTerm (ρ : ℂ) (X T : ℝ) (n : ℕ) : ℂ :=
  (mollifierCoefficient X n : ℂ)*(n : ℂ)^(-ρ)*(Real.exp (-(n : ℝ)/T) : ℂ)

theorem norm_detectorTerm_le {ρ : ℂ} (X : ℝ) {T : ℝ} (n : ℕ)
    (hρ : 0 ≤ ρ.re) :
    ‖detectorTerm ρ X T n‖ ≤ (⌊X⌋₊ : ℝ)*Real.exp (-(n : ℝ)/T) := by
  rw [detectorTerm, ← smoothedDetector_term_eq ρ X T n, norm_mul, Complex.norm_exp]
  have he : (-((n : ℝ)*(1/T : ℝ)) : ℂ).re = -(n : ℝ)/T := by
    simp only [← Complex.ofReal_mul,
      ← Complex.ofReal_neg, Complex.ofReal_re]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right (norm_mollifier_LSeries_term_le_cutoff X n hρ) (by positivity)

/-- A tail estimate uniform in both coordinates of rho on Re(rho)>=0. -/
theorem norm_detector_tail_le {ρ : ℂ} (X : ℝ) {T : ℝ} (K : ℕ)
    (hT : 0 < T) (hρ : 0 ≤ ρ.re) :
    ‖∑' n : ℕ, detectorTerm ρ X T (n+K)‖ ≤
      (⌊X⌋₊ : ℝ)*Real.exp (-(K : ℝ)/T)*(1-Real.exp (-1/T))⁻¹ := by
  let r := Real.exp (-1/T)
  have hr : 0 ≤ r := (Real.exp_pos _).le
  have hr' : r < 1 := Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hT)
  have hg := (hasSum_geometric_of_lt_one hr hr').mul_left
    ((⌊X⌋₊ : ℝ)*Real.exp (-(K : ℝ)/T))
  have hb : ∀ n : ℕ, ‖detectorTerm ρ X T (n+K)‖ ≤
      (⌊X⌋₊ : ℝ)*Real.exp (-(K : ℝ)/T)*r^n := by
    intro n
    have he : Real.exp (-((n+K : ℕ) : ℝ)/T) = Real.exp (-(K : ℝ)/T)*r^n := by
      rw [← Real.exp_nat_mul]
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    exact (norm_detectorTerm_le X (n+K) hρ).trans_eq (by rw [he]; ring)
  have hn := hg.summable.of_nonneg_of_le (fun n => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hn).trans ((hn.tsum_le_tsum hb hg.summable).trans_eq hg.tsum_eq)

/-- The reciprocal geometric denominator costs at most 2T for T>=1. -/
theorem detector_geometric_factor_le {T : ℝ} (hT : 1 ≤ T) :
    (1-Real.exp (-1/T))⁻¹ ≤ 2*T := by
  have hTpos : 0 < T := by linarith
  have he := Real.add_one_le_exp (1/T)
  have hp : 0 < Real.exp (1/T) := Real.exp_pos _
  have hq : Real.exp (-1/T) = (Real.exp (1/T))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
  have hd : 0 < 1-Real.exp (-1/T) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hTpos))
  rw [← one_div]
  apply (div_le_iff₀ hd).2
  rw [hq]
  have hmul : (1/T+1)*T ≤ Real.exp (1/T)*T := mul_le_mul_of_nonneg_right he hTpos.le
  have hone : (1/T+1)*T = 1+T := by field_simp
  rw [hone] at hmul
  have hinv : Real.exp (1/T)*(Real.exp (1/T))⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  have hmul' := mul_le_mul_of_nonneg_right hmul (inv_nonneg.mpr hp.le)
  nlinarith [mul_nonneg (show 0 ≤ T-1 by linarith) (show 0 ≤ 1-(Real.exp (1/T))⁻¹ by simpa [hq] using hd.le)]

/-- The original logarithmic cutoff, with terms retained for n<K. -/
def firstDetectorCutoff (T : ℝ) : ℕ := ⌈T*(Real.log T)^2⌉₊

/-- Quantitative truncation; no zeta or Weyl bound is used. -/
theorem norm_firstDetector_tail_le {ρ : ℂ} {T : ℝ}
    (hT : 1 ≤ T) (hlog : 4 ≤ Real.log T) (hρ : 0 ≤ ρ.re) :
    ‖∑' n : ℕ, detectorTerm ρ (firstDetectorX T) T (n+firstDetectorCutoff T)‖ ≤
      4*T^(-2 : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hX : 0 ≤ firstDetectorX T := by unfold firstDetectorX; positivity
  have hXle : (⌊firstDetectorX T⌋₊ : ℝ) ≤ 2*T := by
    apply (Nat.floor_le hX).trans
    dsimp [firstDetectorX]
    have h := Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (1/8 : ℝ) ≤ 1)
    simpa using mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  have hk : T*(Real.log T)^2 ≤ (firstDetectorCutoff T : ℝ) := Nat.le_ceil _
  have hexp : Real.exp (-(firstDetectorCutoff T : ℝ)/T) ≤ T^(-4 : ℝ) := by
    rw [Real.rpow_def_of_pos hTpos]
    apply Real.exp_le_exp.mpr
    have hq : (Real.log T)^2 ≤ (firstDetectorCutoff T : ℝ)/T := (le_div_iff₀ hTpos).2 (by nlinarith)
    rw [neg_div]
    nlinarith [mul_nonneg (show 0 ≤ Real.log T by linarith) (show 0 ≤ Real.log T-4 by linarith)]
  calc
    _ ≤ (⌊firstDetectorX T⌋₊ : ℝ)*Real.exp (-(firstDetectorCutoff T : ℝ)/T)*(1-Real.exp (-1/T))⁻¹ :=
      norm_detector_tail_le _ _ hTpos hρ
    _ ≤ (2*T)*T^(-4 : ℝ)*(2*T) := by
      apply mul_le_mul _ (detector_geometric_factor_le hT) (le_of_lt (inv_pos.mpr (sub_pos.mpr (Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) hTpos))))) (by positivity)
      exact mul_le_mul hXle hexp (by positivity) (by positivity)
    _ = 4*T^(-2 : ℝ) := by
      have he : T^(-4 : ℝ)*T^2 = T^(-2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hTpos]; norm_num
      nlinarith [he]

/-- One truncation threshold works for every rho with nonnegative real part. -/
theorem firstDetector_tail_eventually_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ, 0 ≤ ρ.re →
      ‖∑' n : ℕ, detectorTerm ρ (firstDetectorX T) T (n+firstDetectorCutoff T)‖ < δ := by
  have ht := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 2 by norm_num)).const_mul 4
  simp only [mul_zero] at ht
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4 : ℝ)),
    ht.eventually (gt_mem_nhds hδ)] with T hT hlog hsmall
  intro ρ hρ
  exact (norm_firstDetector_tail_le hT hlog hρ).trans_lt hsmall

end MathCollab.Density
