module
public import MathCollab.Density.DetectorPoweredPieces

@[expose] public section

open Real Complex Set Filter
open scoped BigOperators Topology ComplexConjugate
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Conjugated genuine convolution coefficients retain uniform divisor growth. -/
theorem poweredDetectorCoefficient_subpower {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (T : ℝ) (N j k n : ℕ),
      0 < T → 0 < N → k ≤ 4 → 0 < n →
        ‖poweredDetectorCoefficient T N j k n‖ ≤ A*(n : ℝ)^δ := by
  obtain ⟨C, hC, hd⟩ := divisor_card_subpower (show 0 < δ/8 by positivity)
  refine ⟨C^8, one_le_pow₀ hC, ?_⟩
  intro T N j k n hT hN hk hn
  have hcard : (1 : ℝ) ≤ n.divisors.card := by
    have hc : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn.ne'⟩
    exact_mod_cast hc
  calc
    _ = ‖((detectorBlockCoefficients T N j)^k) n‖ := norm_conj _
    _ ≤ (n.divisors.card : ℝ)^(2*k) := arithmeticFunction_pow_norm_le
      (detectorBlockCoefficients_norm_le hT hN j) k n
    _ ≤ (n.divisors.card : ℝ)^8 := pow_le_pow_right₀ hcard (by omega)
    _ ≤ (C*(n : ℝ)^(δ/8))^8 := pow_le_pow_left₀ (by positivity) (hd n hn) _
    _ = C^8*(n : ℝ)^δ := by
      rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
      norm_num

/-- The logarithmic ambient enlargement is eventually below T squared. -/
theorem densityAmbient_eventually_le_sq :
    ∀ᶠ T : ℝ in atTop, densityAmbient T ≤ T^2 := by
  have hl := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1 by norm_num)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1/32 by norm_num))] with T hT hlog
  have hh := (div_lt_iff₀ (by linarith : 0 < T)).mp hlog
  unfold densityAmbient
  nlinarith

/-- One threshold works before all block indices, powers and coefficients. -/
theorem poweredDetectorCoefficient_eventually_le {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ N j k n : ℕ,
      0 < N → k ≤ 4 → (n : ℝ) ≤ densityAmbient T →
        ‖poweredDetectorCoefficient T N j k n‖ ≤ T^η := by
  obtain ⟨A, hA, ha⟩ := poweredDetectorCoefficient_subpower (show 0 < η/4 by positivity)
  filter_upwards [eventually_ge_atTop (1 : ℝ), densityAmbient_eventually_le_sq,
    (tendsto_rpow_atTop (show 0 < η/2 by positivity)).eventually_ge_atTop A]
    with T hT hH hlarge
  intro N j k n hN hk hn
  by_cases hn0 : n = 0
  · subst n
    simp [poweredDetectorCoefficient]
    positivity
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  have hTpos : 0 < T := by linarith
  calc
    _ ≤ A*(n : ℝ)^(η/4) := ha T N j k n hTpos hN hk hnpos
    _ ≤ A*(T^2)^(η/4) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) (hn.trans hH) (by positivity)) (by linarith)
    _ = A*T^(η/2) := by
      rw [← Real.rpow_natCast_mul hTpos.le]
      congr 1
      congr 1
      norm_num
      ring
    _ ≤ T^(η/2)*T^(η/2) := mul_le_mul_of_nonneg_right hlarge (by positivity)
    _ = T^η := by rw [← Real.rpow_add hTpos]; congr 1; ring

/-- Coefficient normalization is fixed at T and eta, independently of the zero. -/
def normalizedPoweredCoefficient (η T : ℝ) (N j k n : ℕ) : ℂ :=
  poweredDetectorCoefficient T N j k n / ((T^η : ℝ) : ℂ)

theorem normalizedPoweredCoefficient_eventually {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ N j k n : ℕ,
      0 < N → k ≤ 4 → (n : ℝ) ≤ densityAmbient T →
        ‖normalizedPoweredCoefficient η T N j k n‖ ≤ 1 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), poweredDetectorCoefficient_eventually_le hη]
    with T hT hb
  intro N j k n hN hk hn
  rw [normalizedPoweredCoefficient, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _), div_le_one (by positivity)]
  exact hb N j k n hN hk hn

theorem detectingPolynomial_normalizedPowered (η T t : ℝ) (N j k L : ℕ) :
    detectingPolynomial L (normalizedPoweredCoefficient η T N j k) t =
      detectingPolynomial L (poweredDetectorCoefficient T N j k) t/((T^η : ℝ) : ℂ) := by
  simp only [detectingPolynomial, normalizedPoweredCoefficient, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro n _
  ring

end MathCollab.Density
