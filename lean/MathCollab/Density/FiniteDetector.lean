module
public import MathCollab.Density.DetectorTruncation

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Fixed at each scale T: independent of both coordinates of the zero. -/
def firstDetectorCoefficient (T : ℝ) (n : ℕ) : ℂ :=
  if ⌊firstDetectorX T⌋₊ < n ∧ n < firstDetectorCutoff T then
    (mollifierCoefficient (firstDetectorX T) n : ℂ)*(Real.exp (-(n : ℝ)/T) : ℂ)
  else 0

/-- A finite detector with fixed coefficients; its beta dependence remains
in n^(-rho) until the separate Taylor-family reduction. -/
def finiteDetector (ρ : ℂ) (T : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (firstDetectorCutoff T), firstDetectorCoefficient T n*(n : ℂ)^(-ρ)

theorem firstDetectorCoefficient_support {T : ℝ} {n : ℕ}
    (hn : firstDetectorCoefficient T n ≠ 0) :
    ⌊firstDetectorX T⌋₊ < n ∧ n < firstDetectorCutoff T := by
  by_contra h
  simp [firstDetectorCoefficient, h] at hn

/-- The cutoff convention retains only X<n<T(log T)^2, including all integer
rounding cases. -/
theorem firstDetectorCoefficient_real_support {T : ℝ} {n : ℕ}
    (hT : 0 < T) (hn : firstDetectorCoefficient T n ≠ 0) :
    firstDetectorX T < (n : ℝ) ∧ (n : ℝ) < T*(Real.log T)^2 := by
  have hs := firstDetectorCoefficient_support hn
  exact ⟨(Nat.floor_lt (by unfold firstDetectorX; positivity)).mp hs.1, Nat.lt_ceil.mp hs.2⟩

theorem firstDetectorCoefficient_norm_le {T : ℝ} (hT : 0 < T) (n : ℕ) :
    ‖firstDetectorCoefficient T n‖ ≤ (n.divisors.card : ℝ) := by
  unfold firstDetectorCoefficient
  split_ifs with h
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-(n : ℝ)/T) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) hT.le)
    exact (mul_le_mul (mollifierCoefficient_norm_le _ _) he (by positivity) (by positivity)).trans_eq (mul_one _)
  · simp

theorem firstDetectorX_one_le {T : ℝ} (hT : 1 ≤ T) : 1 ≤ firstDetectorX T := by
  have h := Real.one_le_rpow hT (show (0 : ℝ) ≤ 1/8 by norm_num)
  dsimp [firstDetectorX]
  linarith

theorem detectorTerm_finite_split {T : ℝ} (hT : 1 ≤ T) (ρ : ℂ) {n : ℕ}
    (hn : n < firstDetectorCutoff T) :
    detectorTerm ρ (firstDetectorX T) T n =
      (if n = 1 then (Real.exp (-1/T) : ℂ) else 0) +
      firstDetectorCoefficient T n*(n : ℂ)^(-ρ) := by
  have hX := firstDetectorX_one_le hT
  by_cases hlow : n ≤ ⌊firstDetectorX T⌋₊
  · have hc : firstDetectorCoefficient T n = 0 := by simp [firstDetectorCoefficient, not_lt.mpr hlow]
    rw [hc, zero_mul, add_zero]
    by_cases hn0 : n = 0
    · subst n
      have hz : mollifierCoefficient (firstDetectorX T) 0 = 0 := by simp [mollifierCoefficient]
      simp [detectorTerm, hz]
    · by_cases hn1 : n = 1
      · subst n
        simp [detectorTerm, mollifierCoefficient_one hX]
      · have hnX : (n : ℝ) ≤ firstDetectorX T := (Nat.cast_le.mpr hlow).trans (Nat.floor_le (by linarith))
        simp [detectorTerm, mollifierCoefficient_vanishes (by omega : 2 ≤ n) hnX, hn1]
  · have hn1 : n ≠ 1 := by
      intro he
      subst n
      exact hlow (Nat.le_floor (by simpa using hX))
    simp only [hn1, ite_false, zero_add]
    rw [firstDetectorCoefficient, ite_eq_left ⟨by omega, hn⟩]
    dsimp [detectorTerm]
    ring

/-- Exact subtraction of n=1 and all cancelled terms, with the logarithmic
cutoff's tail still visible. -/
theorem finiteDetector_decomposition {T : ℝ} (hT : 1 ≤ T)
    (hK : 1 < firstDetectorCutoff T) {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    (Real.exp (-1/T) : ℂ) + finiteDetector ρ T +
      (∑' n : ℕ, detectorTerm ρ (firstDetectorX T) T (n+firstDetectorCutoff T)) =
        smoothedDetector ρ (firstDetectorX T) (1/T) := by
  have hs := summable_zeta_detector_series (firstDetectorX T) (by linarith : 0 < T) hρ
  have he := hs.sum_add_tsum_nat_add (firstDetectorCutoff T)
  have hsum : ∑ n ∈ Finset.range (firstDetectorCutoff T), detectorTerm ρ (firstDetectorX T) T n =
      (Real.exp (-1/T) : ℂ)+finiteDetector ρ T := by
    simp_rw [Finset.sum_congr rfl (fun n hn => detectorTerm_finite_split hT ρ (Finset.mem_range.mp hn)), Finset.sum_add_distrib]
    simp [finiteDetector, hK]
  have hfull : (∑' n : ℕ, detectorTerm ρ (firstDetectorX T) T n) =
      smoothedDetector ρ (firstDetectorX T) (1/T) := by
    apply tsum_congr
    intro n
    exact (smoothedDetector_term_eq ρ (firstDetectorX T) T n).symm
  change (∑ n ∈ Finset.range (firstDetectorCutoff T), detectorTerm ρ (firstDetectorX T) T n) +
    (∑' n : ℕ, detectorTerm ρ (firstDetectorX T) T (n+firstDetectorCutoff T)) = (∑' n : ℕ, detectorTerm ρ (firstDetectorX T) T n) at he
  rwa [hsum, hfull] at he

/-- Conditional all-zero finite detection, with unchanged ordinates and fixed
coefficients. Only the displayed actual-zeta growth estimate remains an input. -/
theorem finiteDetector_eventually_large_of_zeta_bound {η C : ℝ}
    (hη : 0 ≤ η) (hη' : η < 1/48) (hC : 0 ≤ C)
    (hW : ∀ t : ℝ, ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ C*(1+|t|)^(1/6+η)) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      3/4 ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 → (1/2 : ℝ) ≤ ‖finiteDetector ρ T‖ := by
  filter_upwards [eventually_ge_atTop (4 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (4 : ℝ)),
    firstDetector_tail_eventually_small (show (0 : ℝ) < 1/8 by norm_num),
    firstDetector_eventually_small_of_zeta_bound hη hη' hC (show (0 : ℝ) < 1/8 by norm_num) hW]
      with T hT hlog htail hsmall
  intro ρ hβ hβ' hγ hγ' hzero
  have hK : 1 < firstDetectorCutoff T := by
    have hk : T*(Real.log T)^2 ≤ (firstDetectorCutoff T : ℝ) := Nat.le_ceil _
    have hs : 16 ≤ (Real.log T)^2 := by nlinarith
    have hr : (1 : ℝ) < firstDetectorCutoff T := by nlinarith
    exact_mod_cast hr
  have hd := finiteDetector_decomposition (by linarith : 1 ≤ T) hK (show 0 ≤ ρ.re by linarith)
  have hfirst : (3/4 : ℝ) ≤ Real.exp (-1/T) := by
    have he := Real.add_one_le_exp (-1/T)
    have hi : 1/T ≤ (1/4 : ℝ) := (div_le_iff₀ (by linarith : 0 < T)).2 (by linarith)
    rw [neg_div] at he ⊢
    linarith
  have hnorm : ‖(Real.exp (-1/T) : ℂ)‖ ≤ ‖smoothedDetector ρ (firstDetectorX T) (1/T)‖ +
      ‖finiteDetector ρ T‖ + ‖∑' n : ℕ, detectorTerm ρ (firstDetectorX T) T (n+firstDetectorCutoff T)‖ := by
    have he : (Real.exp (-1/T) : ℂ) = smoothedDetector ρ (firstDetectorX T) (1/T) - finiteDetector ρ T -
      (∑' n : ℕ, detectorTerm ρ (firstDetectorX T) T (n+firstDetectorCutoff T)) := by rw [← hd]; ring
    rw [he]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hnorm
  have ht := htail ρ (by linarith)
  have hm := hsmall ρ hβ hβ' hγ hγ' hzero
  linarith

end MathCollab.Density
