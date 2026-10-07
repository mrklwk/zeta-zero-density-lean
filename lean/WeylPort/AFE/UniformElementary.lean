module
public import WeylPort.AFE.HarmonicDigamma
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

namespace WeylPort
open Filter
open scoped Topology

/-- The dual cutoff gap keeps the actual digamma value in a fixed bounded interval. -/
theorem digamma_gap_bounds {δ : ℝ} (hδ : 1/2 ≤ δ) (hδ1 : δ ≤ 1) :
    -4 ≤ (Complex.digamma (δ : ℂ)).re ∧ (Complex.digamma (δ : ℂ)).re ≤ 0 := by
  have hδ0 : 0 < δ := by linarith
  have hi : 1 / δ ≤ 2 := (div_le_iff₀ hδ0).mpr (by linarith)
  have hl := Real.one_sub_inv_le_log_of_pos hδ0
  have hb := DhimanKadiriQuesadaHerrera2026.real_digamma_bounds hδ0
  have hu : Real.log δ ≤ 0 := Real.log_nonpos hδ0.le hδ1
  have hp : 0 ≤ 1 / (2 * δ) := by positivity
  constructor <;> simp only [one_div] at * <;> linarith

/-- The logarithm in the lower-integral error is uniformly absorbed by its weight. -/
theorem weighted_log_cutoff_le {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x) :
    x ^ (-(1/2 : ℝ)) * (1 + Real.log y) ≤ 3 := by
  have hx0 : 0 < x := by linarith
  have hw : 0 ≤ x ^ (-(1/2 : ℝ)) := Real.rpow_nonneg hx0.le _
  have hw1 : x ^ (-(1/2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hlog := (Real.log_le_log (by linarith : 0 < y) hyx).trans
    (Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1/2))
  have hprod : x ^ (-(1/2 : ℝ)) * x ^ (1/2 : ℝ) = 1 := by
    rw [← Real.rpow_add hx0]; norm_num
  have hh := mul_le_mul_of_nonneg_left hlog hw
  nlinarith

/-- Exponential Gamma errors times a quadratic envelope tend to zero. -/
theorem eventually_gamma_envelope_le_one :
    ∀ᶠ t : ℝ in atTop, Real.exp (-Real.pi * t) * (t ^ 2 + 1) ≤ 1 := by
  have hpoly := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hexp := Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hlim : Tendsto (fun t : ℝ => (t ^ 2 + 1) * Real.exp (-t)) atTop (𝓝 0) := by
    simpa only [add_mul, one_mul, zero_add, Function.comp_def] using hpoly.add hexp
  filter_upwards [eventually_ge_atTop (0 : ℝ), hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht hlimt
  have he : Real.exp (-Real.pi * t) ≤ Real.exp (-t) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_gt_three]
  exact (mul_le_mul_of_nonneg_right he (by positivity)).trans (by simpa only [mul_comm] using hlimt.le)

end WeylPort
