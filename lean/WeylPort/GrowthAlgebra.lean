module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
Pure scale algebra extracted from S. McColm, commit
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1 (MIT-0).
ZetaSourceLogScales: eventually_const_log_pow_le_rpow;
PointValueGrowth: its first four theorems.
The actual-zeta theorem is deliberately absent: its analytic input is not ported.
-/

noncomputable section
open Filter
namespace TaoTrudgianYang2025

theorem eventually_const_log_pow_le_rpow (C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, C * (Real.log T) ^ k ≤ T ^ η := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hη).const_mul_left C
  filter_upwards [hsmall.bound (by norm_num : (0 : ℝ) < 1), eventually_ge_atTop (1 : ℝ)] with T h hT
  simpa only [Real.rpow_natCast, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (mul_nonneg hC (pow_nonneg (Real.log_nonneg hT) k)),
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) η)] using h

theorem eventually_const_height_log_pow_mul_rpow_le_rpow
    {C a b : ℝ} (hC : 0 ≤ C) (k : ℕ) (hab : a < b) :
    ∀ᶠ H : ℝ in atTop,
      C*(Real.log (3*H))^k*H^a ≤ H^b := by
  have hs := eventually_const_log_pow_le_rpow (C*2^k) (by positivity)
    k (sub_pos.mpr hab)
  filter_upwards [hs,eventually_ge_atTop (3:ℝ)] with H hs hH
  have hH0 : 0 < H := by linarith
  have hlog3 : Real.log 3 ≤ Real.log H :=
    Real.log_le_log (by norm_num) hH
  have hlog : Real.log (3*H) ≤ 2*Real.log H := by
    rw [Real.log_mul (by norm_num) hH0.ne']
    linarith
  have hp := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.log_nonneg (by linarith : 1 ≤ 3*H)) hlog k) hC
  rw [mul_pow] at hp
  have hsmall : C*(Real.log (3*H))^k ≤ H^(b-a) := by
    exact hp.trans (by nlinarith [hs])
  calc
    C*(Real.log (3*H))^k*H^a ≤ H^(b-a)*H^a :=
      mul_le_mul_of_nonneg_right hsmall (by positivity)
    _ = H^b := by rw [← Real.rpow_add hH0]; congr 1; ring

theorem pointValue_sixth_power_count_identity {D L H η : ℝ}
    (hH : 0 < H) :
    D*H^η*(H*L^4/(H^(1/6+η))^6+H^2*L^6/(H^(1/6+η))^12) =
      D*L^4/H^(5*η)+D*L^6/H^(11*η) := by
  have h6 : (H^(1/6+η))^6 = H^η*H*H^(5*η) := by
    calc
      (H^(1/6+η))^6 = H^((1/6+η)*(6:ℝ)) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hH.le]
        norm_num
      _ = H^(η+1+5*η) := by congr 1; ring
      _ = H^η*H*H^(5*η) := by rw [Real.rpow_add hH,Real.rpow_add hH,Real.rpow_one]
  have h12 : (H^(1/6+η))^12 = H^η*H^2*H^(11*η) := by
    calc
      (H^(1/6+η))^12 = H^((1/6+η)*(12:ℝ)) := by
        rw [← Real.rpow_natCast,← Real.rpow_mul hH.le]
        norm_num
      _ = H^(η+2+11*η) := by congr 1; ring
      _ = H^η*H^2*H^(11*η) := by rw [Real.rpow_add hH,Real.rpow_add hH,Real.rpow_two]
  rw [h6,h12]
  field_simp

theorem eventually_pointValue_sixth_power_count_lt_one
    {D η : ℝ} (hD : 0 < D) (hη : 0 < η) :
    ∀ᶠ H : ℝ in atTop,
      D*H^η*(H*(Real.log (3*H))^4/(H^(1/6+η))^6 +
        H^2*(Real.log (3*H))^6/(H^(1/6+η))^12) < 1 := by
  have h4 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 4*D) (a := 0) (b := 5*η) (by positivity) 4 (by linarith)
  have h6 := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := 4*D) (a := 0) (b := 11*η) (by positivity) 6 (by linarith)
  filter_upwards [h4,h6,eventually_gt_atTop (0:ℝ)] with H h4 h6 hH
  rw [Real.rpow_zero,mul_one] at h4 h6
  have hfirst : D*(Real.log (3*H))^4/H^(5*η) ≤ 1/4 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [h4])
  have hsecond : D*(Real.log (3*H))^6/H^(11*η) ≤ 1/4 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [h6])
  rw [pointValue_sixth_power_count_identity hH]
  linarith

theorem eventually_pointValue_sixth_power_source_range
    {K η : ℝ} (hK : 0 < K) (hη : 0 < η) (hηUpper : η ≤ 1/48) :
    ∀ᶠ H : ℝ in atTop,
      K*(Real.log (3*H))^2*(2*H)^(1/4+(1/48:ℝ)) ≤
          (H^(1/6+η))^2 ∧
      (H^(1/6+η))^2 ≤
        K*(Real.log (3*H))^2*H^(1/2-(1/48:ℝ)) := by
  let q : ℝ := 1/4+(1/48:ℝ)
  let r : ℝ := 1/2-(1/48:ℝ)
  have hlower := eventually_const_height_log_pow_mul_rpow_le_rpow
    (C := K*2^q) (a := q) (b := 1/3+2*η) (by positivity) 2
    (by dsimp only [q]; linarith)
  have hlog := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (max 1 (1/K)))
  filter_upwards [hlower,hlog,eventually_ge_atTop (3:ℝ)] with H hlower hlog hH
  have hH0 : 0 < H := by linarith
  have hH1 : 1 ≤ H := by linarith
  have hLmono : Real.log H ≤ Real.log (3*H) :=
    Real.log_le_log hH0 (by linarith)
  have hL1 : 1 ≤ Real.log (3*H) := ((le_max_left _ _).trans hlog).trans hLmono
  have hKL : 1 ≤ K*Real.log (3*H) := by
    have hr : 1/K ≤ Real.log (3*H) :=
      ((le_max_right _ _).trans hlog).trans hLmono
    have hp := (div_le_iff₀ hK).mp hr
    nlinarith
  have hKL2 : 1 ≤ K*(Real.log (3*H))^2 := by
    have hp := mul_le_mul_of_nonneg_right hL1 (by positivity : 0 ≤ K*Real.log (3*H))
    nlinarith
  have hp : (H^(1/6+η))^2 = H^(1/3+2*η) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hH0.le]
    congr 1
    norm_num
    ring
  rw [hp]
  constructor
  · have htwo : (2*H)^q = 2^q*H^q :=
      Real.mul_rpow (by norm_num) hH0.le
    change K*(Real.log (3*H))^2*(2*H)^q ≤ _
    rw [htwo]
    nlinarith [hlower]
  · calc
      H^(1/3+2*η) ≤ H^r :=
        Real.rpow_le_rpow_of_exponent_le hH1 (by dsimp only [r]; linarith)
      _ ≤ K*(Real.log (3*H))^2*H^r := by
        have hh := mul_le_mul_of_nonneg_right hKL2 (by positivity : 0 ≤ H^r)
        simpa only [one_mul] using hh

end TaoTrudgianYang2025
