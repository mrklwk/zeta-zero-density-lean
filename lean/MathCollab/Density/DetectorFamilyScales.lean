module
public import MathCollab.Density.DetectorDyadic
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

open Real Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

def detectorTaylorCutoff (T : ℝ) : ℕ := ⌈10*Real.log T⌉₊

/-- A coarse natural-cutoff bound, sufficient for all family counts. -/
theorem firstDetectorCutoff_eventually_le_sq :
    ∀ᶠ T : ℝ in atTop, (firstDetectorCutoff T : ℝ) ≤ T^2 := by
  have hl := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (2 : ℝ), hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))] with T hT hlog
  have hTpos : 0 < T := by linarith
  have hq : (Real.log T)^2 < T/2 := (div_lt_iff₀ hTpos).mp hlog |>.trans_eq (by ring)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ T*(Real.log T)^2 by positivity)
  change (firstDetectorCutoff T : ℝ) < T*(Real.log T)^2+1 at hc
  nlinarith

/-- Explicit O(log T) size of the fixed dyadic list. -/
theorem detectorDyadicCount_le_log {T : ℝ} (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T)
    (hK : (firstDetectorCutoff T : ℝ) ≤ T^2) :
    (detectorDyadicCount T : ℝ) ≤ 5*Real.log T := by
  let K := firstDetectorCutoff T
  have hTpos : 0 < T := by linarith
  have hKpos : 0 < K := by
    apply Nat.ceil_pos.mpr
    exact mul_pos hTpos (sq_pos_of_pos (by linarith))
  have hp : (2 : ℝ)^(Nat.log 2 K) ≤ (K : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hKpos.ne'
  have hl := (Real.log_le_log (by positivity) hp).trans (Real.log_le_log (by exact_mod_cast hKpos) hK)
  rw [Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have htwo : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hnonneg : (0 : ℝ) ≤ Nat.log 2 K := by positivity
  have hprod := mul_le_mul_of_nonneg_left htwo hnonneg
  change ((Nat.log 2 K+1 : ℕ) : ℝ) ≤ _
  push_cast
  linarith

theorem detectorTaylorCutoff_le_log {T : ℝ} (hlog : 1 ≤ Real.log T) :
    (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T := by
  have h := Nat.ceil_lt_add_one (show 0 ≤ 10*Real.log T by linarith)
  change (detectorTaylorCutoff T : ℝ) < 10*Real.log T+1 at h
  linarith

/-- The chosen Taylor cutoff gives a polynomially small geometric factor. -/
theorem detectorTaylorCutoff_geometric_le {T : ℝ} (hT : 1 ≤ T) :
    (1/3 : ℝ)^(detectorTaylorCutoff T) ≤ T^(-5 : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  have hJ : 10*Real.log T ≤ (detectorTaylorCutoff T : ℝ) := Nat.le_ceil _
  have h3 : (1/2 : ℝ) ≤ Real.log 3 := by
    have hm := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≤ 3)
    linarith [Real.log_two_gt_d9]
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hTpos]
  apply Real.exp_le_exp.mpr
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  nlinarith [mul_le_mul_of_nonneg_right h3 (show 0 ≤ (detectorTaylorCutoff T : ℝ) by positivity)]

/-- All scales are selected before beta, gamma or an actual zero varies. -/
theorem detector_family_scales_eventually :
    ∀ᶠ T : ℝ in atTop, 2 ≤ T ∧ 1 ≤ Real.log T ∧
      (firstDetectorCutoff T : ℝ) ≤ T^2 ∧
      (detectorDyadicCount T : ℝ) ≤ 5*Real.log T ∧
      (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T ∧
      3*T^(-1 : ℝ) ≤ 1/(4*(detectorDyadicCount T : ℝ)) := by
  have ht := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  norm_num at ht
  filter_upwards [eventually_ge_atTop (2 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    firstDetectorCutoff_eventually_le_sq, ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1/60 by norm_num))]
    with T hT hlog hK hsmall
  have hD := detectorDyadicCount_le_log (by linarith) hlog hK
  refine ⟨hT, hlog, hK, hD, detectorTaylorCutoff_le_log hlog, ?_⟩
  have hTpos : 0 < T := by linarith
  have hDpos : (0 : ℝ) < detectorDyadicCount T := by unfold detectorDyadicCount; positivity
  rw [Real.rpow_neg_one, ← one_div]
  apply (le_div_iff₀ (by positivity : 0 < 4*(detectorDyadicCount T : ℝ))).2
  have hl : Real.log T < T/60 := (div_lt_iff₀ hTpos).mp hsmall |>.trans_eq (by ring)
  rw [show 3*(1/T)*(4*(detectorDyadicCount T : ℝ)) = 12*(detectorDyadicCount T : ℝ)/T by ring]
  apply (div_le_iff₀ hTpos).2
  nlinarith

end MathCollab.Density
