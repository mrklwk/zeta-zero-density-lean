module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.PowerWeights

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Actual AFE second derivatives and positive-frequency quotients

The four quotient conditions are proved for the power weight and logarithmic
phase on their positive domain, including nonnegative σ and its zero boundary.
The general theorem exposes the additional hypotheses in CorrectedPartII.
-/

namespace DhimanKadiriQuesadaHerrera2026

/-- The true second derivative of the AFE power weight on the positive half-line. -/
theorem afeWeight_deriv_hasDerivAt (σ : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (deriv (afeWeight σ)) (σ * (σ + 1) * u ^ (-σ - 2)) u := by
  have hd := (Real.hasDerivAt_rpow_const (p := -σ - 1) (Or.inl hu.ne')).const_mul (-σ)
  have he : -σ * ((-σ - 1) * u ^ (-σ - 1 - 1)) = σ * (σ + 1) * u ^ (-σ - 2) := by
    rw [show -σ - 1 - 1 = -σ - 2 by ring]
    ring
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with v hv
  exact (afeWeight_hasDerivAt σ hv).deriv

/-- The logarithmic phase has its actual second derivative. -/
theorem afePhase_deriv_hasDerivAt (c : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (deriv (afePhase c)) (-c / u ^ 2) u := by
  have hd : HasDerivAt (fun v : ℝ => c / v) (-c / u ^ 2) u := by
    simpa only [id_eq, zero_mul, mul_one, zero_sub, neg_div] using
      (hasDerivAt_const u c).fun_div (hasDerivAt_id u) hu.ne'
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hu] with v hv
  exact (afePhase_hasDerivAt c hv).deriv

/-- The positive-frequency denominator cancels the exact power of the integration variable. -/
theorem afe_power_quotient_normalize {σ c ν u : ℝ} (hc : 0 ≤ c) (hν : 0 < ν)
    (hu : 0 < u) (k : ℕ) :
    u ^ (-σ - (k : ℝ)) / (ν + c / u) ^ k = u ^ (-σ) / (ν * u + c) ^ k := by
  rw [Real.rpow_sub_natCast hu.ne']
  have hd : ν * u + c ≠ 0 := ne_of_gt (by positivity)
  have he : ν + c / u = (ν * u + c) / u := by field_simp
  rw [he, div_pow]
  field_simp

/-- The normalized quotient is decreasing for every nonnegative σ, including the constant-weight boundary. -/
theorem afe_power_quotient_antitone {σ c ν : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (hν : 0 < ν) (k : ℕ) :
    AntitoneOn (fun u => u ^ (-σ) / (ν * u + c) ^ k) (Set.Ioi 0) := by
  intro u hu v hv huv
  change 0 < u at hu
  change 0 < v at hv
  apply div_le_div₀ (Real.rpow_nonneg hu.le _)
    (Real.rpow_le_rpow_of_nonpos hu huv (neg_nonpos.mpr hσ)) (by positivity)
  exact pow_le_pow_left₀ (by positivity) (by nlinarith) k

/-- The second AFE amplitude uses the derivative of the actual weight-phase product. -/
theorem afeWeight_phaseProduct_hasDerivAt (σ c : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v => afeWeight σ v * deriv (afePhase c) v)
      (-c * (σ + 1) * u ^ (-σ - 2)) u := by
  convert (afeWeight_hasDerivAt σ hu).mul (afePhase_deriv_hasDerivAt c hu) using 1
  rw [(afePhase_hasDerivAt c hu).deriv]
  unfold afeWeight
  rw [Real.rpow_sub_one hu.ne', (show u ^ (-σ - 2) = u ^ (-σ) / u ^ 2 by simpa only [Nat.cast_ofNat] using Real.rpow_sub_natCast hu.ne' (-σ) 2)]
  field_simp
  ring

/-- The first positive-frequency derivative quotient has an explicit decreasing normal form. -/
theorem afe_second_derivative_quotient {σ c ν u : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (hν : 0 < ν) (hu : 0 < u) :
    |deriv (deriv (afeWeight σ)) u| / (ν + deriv (afePhase c) u) ^ 2 =
      σ * (σ + 1) * (u ^ (-σ) / (ν * u + c) ^ 2) := by
  rw [(afeWeight_deriv_hasDerivAt σ hu).deriv, (afePhase_hasDerivAt c hu).deriv,
    abs_of_nonneg (by positivity : 0 ≤ σ * (σ + 1) * u ^ (-σ - 2)), mul_div_assoc,
    (show u ^ (-σ - 2) / (ν + c / u) ^ 2 = u ^ (-σ) / (ν * u + c) ^ 2 by simpa only [Nat.cast_ofNat] using afe_power_quotient_normalize (σ := σ) hc hν hu 2)]

/-- The first positive-frequency curvature quotient has its exact normal form. -/
theorem afe_derivative_curvature_quotient {σ c ν u : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (hν : 0 < ν) (hu : 0 < u) :
    |deriv (afeWeight σ) u * deriv (deriv (afePhase c)) u| /
        (ν + deriv (afePhase c) u) ^ 3 =
      σ * c * (u ^ (-σ) / (ν * u + c) ^ 3) := by
  rw [(afeWeight_hasDerivAt σ hu).deriv, (afePhase_deriv_hasDerivAt c hu).deriv,
    (afePhase_hasDerivAt c hu).deriv]
  have he : (-σ * u ^ (-σ - 1)) * (-c / u ^ 2) = σ * c * u ^ (-σ - 3) := by
    rw [Real.rpow_sub_one hu.ne', (show u ^ (-σ - 3) = u ^ (-σ) / u ^ 3 by simpa only [Nat.cast_ofNat] using Real.rpow_sub_natCast hu.ne' (-σ) 3)]
    field_simp
  rw [he, abs_of_nonneg (by positivity : 0 ≤ σ * c * u ^ (-σ - 3)), mul_div_assoc,
    (show u ^ (-σ - 3) / (ν + c / u) ^ 3 = u ^ (-σ) / (ν * u + c) ^ 3 by simpa only [Nat.cast_ofNat] using afe_power_quotient_normalize (σ := σ) hc hν hu 3)]

/-- The product-amplitude derivative quotient has its exact normal form. -/
theorem afe_product_derivative_quotient {σ c ν u : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (hν : 0 < ν) (hu : 0 < u) :
    |deriv (fun v => afeWeight σ v * deriv (afePhase c) v) u| /
        (ν + deriv (afePhase c) u) ^ 2 =
      c * (σ + 1) * (u ^ (-σ) / (ν * u + c) ^ 2) := by
  rw [(afeWeight_phaseProduct_hasDerivAt σ c hu).deriv, (afePhase_hasDerivAt c hu).deriv,
    abs_of_nonpos (by
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (by linarith))
        (Real.rpow_nonneg hu.le _))]
  rw [show -(-c * (σ + 1) * u ^ (-σ - 2)) = c * (σ + 1) * u ^ (-σ - 2) by ring,
    mul_div_assoc, (show u ^ (-σ - 2) / (ν + c / u) ^ 2 = u ^ (-σ) / (ν * u + c) ^ 2 by simpa only [Nat.cast_ofNat] using afe_power_quotient_normalize (σ := σ) hc hν hu 2)]

/-- The product-amplitude curvature quotient has its exact normal form. -/
theorem afe_product_curvature_quotient {σ c ν u : ℝ} (hc : 0 ≤ c)
    (hν : 0 < ν) (hu : 0 < u) :
    |(afeWeight σ u * deriv (afePhase c) u) * deriv (deriv (afePhase c)) u| /
        (ν + deriv (afePhase c) u) ^ 3 =
      c ^ 2 * (u ^ (-σ) / (ν * u + c) ^ 3) := by
  rw [(afePhase_hasDerivAt c hu).deriv, (afePhase_deriv_hasDerivAt c hu).deriv]
  have he : (afeWeight σ u * (c / u)) * (-c / u ^ 2) = -c ^ 2 * u ^ (-σ - 3) := by
    unfold afeWeight
    rw [(show u ^ (-σ - 3) = u ^ (-σ) / u ^ 3 by simpa only [Nat.cast_ofNat] using Real.rpow_sub_natCast hu.ne' (-σ) 3)]
    field_simp
  rw [he, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg c))
    (Real.rpow_nonneg hu.le _)), neg_mul, neg_neg, mul_div_assoc,
      (show u ^ (-σ - 3) / (ν + c / u) ^ 3 = u ^ (-σ) / (ν * u + c) ^ 3 by simpa only [Nat.cast_ofNat] using afe_power_quotient_normalize (σ := σ) hc hν hu 3)]

/-- All four positive-frequency quotients actually needed by the AFE are nonincreasing.
This discharges the application-specific conditions; it does not assert the printed general inference. -/
theorem afe_second_quotients_antitone {σ c ν : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (hν : 0 < ν) :
    AntitoneOn (fun u => |deriv (deriv (afeWeight σ)) u| /
      (ν + deriv (afePhase c) u) ^ 2) (Set.Ioi 0) ∧
    AntitoneOn (fun u => |deriv (afeWeight σ) u * deriv (deriv (afePhase c)) u| /
      (ν + deriv (afePhase c) u) ^ 3) (Set.Ioi 0) ∧
    AntitoneOn (fun u => |deriv (fun v => afeWeight σ v * deriv (afePhase c) v) u| /
      (ν + deriv (afePhase c) u) ^ 2) (Set.Ioi 0) ∧
    AntitoneOn (fun u => |(afeWeight σ u * deriv (afePhase c) u) * deriv (deriv (afePhase c)) u| /
      (ν + deriv (afePhase c) u) ^ 3) (Set.Ioi 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u hu v hv huv
    dsimp only
    rw [afe_second_derivative_quotient hσ hc hν hu, afe_second_derivative_quotient hσ hc hν hv]
    exact mul_le_mul_of_nonneg_left (afe_power_quotient_antitone hσ hc hν 2 hu hv huv)
      (mul_nonneg hσ (by linarith))
  · intro u hu v hv huv
    dsimp only
    rw [afe_derivative_curvature_quotient hσ hc hν hu, afe_derivative_curvature_quotient hσ hc hν hv]
    exact mul_le_mul_of_nonneg_left (afe_power_quotient_antitone hσ hc hν 3 hu hv huv)
      (mul_nonneg hσ hc)
  · intro u hu v hv huv
    dsimp only
    rw [afe_product_derivative_quotient hσ hc hν hu, afe_product_derivative_quotient hσ hc hν hv]
    exact mul_le_mul_of_nonneg_left (afe_power_quotient_antitone hσ hc hν 2 hu hv huv)
      (mul_nonneg hc (by linarith))
  · intro u hu v hv huv
    dsimp only
    rw [afe_product_curvature_quotient hc hν hu, afe_product_curvature_quotient hc hν hv]
    exact mul_le_mul_of_nonneg_left (afe_power_quotient_antitone hσ hc hν 3 hu hv huv) (sq_nonneg c)

/-- The source's second derivatives and product derivative decrease for the actual AFE functions. -/
theorem afe_second_derivatives_antitone {σ c : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c) :
    AntitoneOn (deriv (deriv (afeWeight σ))) (Set.Ioi 0) ∧
    AntitoneOn (fun u => |deriv (deriv (afePhase c)) u|) (Set.Ioi 0) ∧
    AntitoneOn (fun u => |deriv (fun v => afeWeight σ v * deriv (afePhase c) v) u|)
      (Set.Ioi 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro u hu v hv huv
    rw [(afeWeight_deriv_hasDerivAt σ hu).deriv, (afeWeight_deriv_hasDerivAt σ hv).deriv]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hu huv (by linarith)) (mul_nonneg hσ (by linarith))
  · intro u hu v hv huv
    dsimp only
    rw [(afePhase_deriv_hasDerivAt c hu).deriv, (afePhase_deriv_hasDerivAt c hv).deriv,
      abs_div, abs_div, abs_neg, abs_of_nonneg hc, abs_of_nonneg (sq_nonneg u),
      abs_of_nonneg (sq_nonneg v)]
    exact div_le_div_of_nonneg_left hc (sq_pos_of_pos hu) (pow_le_pow_left₀ hu.le huv 2)
  · intro u hu v hv huv
    dsimp only
    rw [(afeWeight_phaseProduct_hasDerivAt σ c hu).deriv,
      (afeWeight_phaseProduct_hasDerivAt σ c hv).deriv]
    have he (x : ℝ) (hx : 0 < x) : |-c * (σ + 1) * x ^ (-σ - 2)| =
        c * (σ + 1) * x ^ (-σ - 2) := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hc, abs_of_nonneg (by linarith : 0 ≤ σ + 1),
        abs_of_pos (Real.rpow_pos_of_pos hx _)]
    rw [he u hu, he v hv]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hu huv (by linarith)) (mul_nonneg hc (by linarith))

/-- The strict source positivity conditions hold when σ and the height scale are positive. -/
theorem afe_second_derivatives_pos {σ c u : ℝ} (hσ : 0 < σ) (hc : 0 < c) (hu : 0 < u) :
    0 < |deriv (afeWeight σ) u| ∧
    0 < |deriv (deriv (afePhase c)) u| ∧
    0 < deriv (deriv (afeWeight σ)) u ∧
    0 < |deriv (fun v => afeWeight σ v * deriv (afePhase c) v) u| := by
  rw [abs_deriv_afeWeight hσ.le hu, (afePhase_deriv_hasDerivAt c hu).deriv,
    (afeWeight_deriv_hasDerivAt σ hu).deriv, (afeWeight_phaseProduct_hasDerivAt σ c hu).deriv]
  refine ⟨by positivity, ?_, by positivity, ?_⟩
  · rw [abs_div, abs_neg, abs_of_pos hc, abs_of_nonneg (sq_nonneg u)]
    positivity
  · rw [abs_mul, abs_mul, abs_neg, abs_of_pos hc, abs_of_pos (by linarith : 0 < σ + 1),
      abs_of_pos (Real.rpow_pos_of_pos hu _)]
    positivity

/-- Both actual second-integration amplitudes are continuously differentiable on u>0. -/
theorem afe_second_amplitude_regular (σ c : ℝ) (h : ℝ → ℝ)
    (hh : h = deriv (afeWeight σ) ∨ h = fun u => afeWeight σ u * deriv (afePhase c) u) :
    (∀ u ∈ Set.Ioi 0, DifferentiableAt ℝ h u) ∧ ContinuousOn (deriv h) (Set.Ioi 0) := by
  rcases hh with rfl | rfl
  · refine ⟨fun u hu => (afeWeight_deriv_hasDerivAt σ hu).differentiableAt, ?_⟩
    have hc : ContinuousOn (fun u : ℝ => σ * (σ + 1) * u ^ (-σ - 2)) (Set.Ioi 0) := by
      intro u hu
      exact (continuousAt_const.mul
        (Real.continuousAt_rpow_const u (-σ - 2) (Or.inl hu.ne'))).continuousWithinAt
    exact hc.congr (fun u hu => (afeWeight_deriv_hasDerivAt σ hu).deriv)
  · refine ⟨fun u hu => (afeWeight_phaseProduct_hasDerivAt σ c hu).differentiableAt, ?_⟩
    have hc : ContinuousOn (fun u : ℝ => -c * (σ + 1) * u ^ (-σ - 2)) (Set.Ioi 0) := by
      intro u hu
      exact (continuousAt_const.mul
        (Real.continuousAt_rpow_const u (-σ - 2) (Or.inl hu.ne'))).continuousWithinAt
    exact hc.congr (fun u hu => (afeWeight_phaseProduct_hasDerivAt σ c hu).deriv)

/-- Both actual second-integration amplitudes and their absolute derivatives decrease, including σ=0. -/
theorem afe_second_amplitudes_antitone {σ c : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c)
    (h : ℝ → ℝ)
    (hh : h = deriv (afeWeight σ) ∨ h = fun u => afeWeight σ u * deriv (afePhase c) u) :
    AntitoneOn (fun u => |h u|) (Set.Ioi 0) ∧
    AntitoneOn (fun u => |deriv h u|) (Set.Ioi 0) := by
  have hp : AntitoneOn (deriv (afePhase c)) (Set.Ioi 0) := by
    intro u hu v hv huv
    rw [(afePhase_hasDerivAt c hu).deriv, (afePhase_hasDerivAt c hv).deriv]
    exact div_le_div_of_nonneg_left hc hu huv
  have hd := afe_second_derivatives_antitone hσ hc
  rcases hh with rfl | rfl
  · refine ⟨abs_deriv_afeWeight_antitone hσ, ?_⟩
    have hnon (u : ℝ) (hu : 0 < u) : 0 ≤ deriv (deriv (afeWeight σ)) u := by
      rw [(afeWeight_deriv_hasDerivAt σ hu).deriv]
      positivity
    intro u hu v hv huv
    dsimp only
    rw [abs_of_nonneg (hnon u hu), abs_of_nonneg (hnon v hv)]
    exact hd.1 hu hv huv
  · refine ⟨?_, hd.2.2⟩
    have hnon (u : ℝ) (hu : 0 < u) : 0 ≤ afeWeight σ u * deriv (afePhase c) u := by
      rw [(afePhase_hasDerivAt c hu).deriv]
      exact mul_nonneg (afeWeight_pos σ hu).le (div_nonneg hc hu.le)
    intro u hu v hv huv
    dsimp only
    rw [abs_of_nonneg (hnon u hu), abs_of_nonneg (hnon v hv)]
    exact mul_le_mul (afeWeight_antitone hσ hu hv huv) (hp hu hv huv)
      (by rw [(afePhase_hasDerivAt c hv).deriv]; exact div_nonneg hc hv.le) (afeWeight_pos σ hu).le


end DhimanKadiriQuesadaHerrera2026
