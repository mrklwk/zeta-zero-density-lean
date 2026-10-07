module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.AFESecondModes
public import WeylPort.AFE.PoissonApplications

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Exact amplitude-series assembly for the Poisson remainder

The AFE consumer derives all four convergence inputs from the actual functions.
The corrected general Part-II error contract is exposed in CorrectedPartII.
-/

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory
/-- Split the actual derivative-amplitude integral into its two real amplitudes. -/
theorem derivativeMode_eq_amplitude_integrals {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (ν : ℝ) :
    derivativeMode f g a b ν =
      (∫ u in a..b, ((deriv g u : ℝ) : ℂ) *
        exp (2 * (Real.pi : ℂ) * I * ((f u - ν * u : ℝ) : ℂ))) +
      (2 * (Real.pi : ℂ) * I) *
        (∫ u in a..b, ((g u * deriv f u : ℝ) : ℂ) *
          exp (2 * (Real.pi : ℂ) * I * ((f u - ν * u : ℝ) : ℂ))) := by
  have he : ContinuousOn (fun u => exp (2 * (Real.pi : ℂ) * I * ((f u - ν * u : ℝ) : ℂ))) (Set.Icc a b) :=
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (h.f_continuous.sub (continuousOn_const.mul continuousOn_id)))).cexp
  have hi1 : IntervalIntegrable (fun u => ((deriv g u : ℝ) : ℂ) *
      exp (2 * (Real.pi : ℂ) * I * ((f u - ν * u : ℝ) : ℂ))) volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn h.g_deriv_continuous).mul he).intervalIntegrable_of_Icc h.lt.le
  have hi2 : IntervalIntegrable (fun u => ((g u * deriv f u : ℝ) : ℂ) *
      exp (2 * (Real.pi : ℂ) * I * ((f u - ν * u : ℝ) : ℂ))) volume a b :=
    ((Complex.continuous_ofReal.comp_continuousOn (h.g_continuous.mul h.f_deriv_continuous)).mul he).intervalIntegrable_of_Icc h.lt.le
  unfold derivativeMode
  have hs := intervalIntegral.integral_add hi1 (hi2.const_mul (2 * (Real.pi : ℂ) * I))
  rw [intervalIntegral.integral_const_mul] at hs
  simpa only [add_mul, mul_assoc] using hs

private theorem amplitude_coefficient_normalize (A B d : ℂ) :
    (A + (2 * (Real.pi : ℂ) * I) * B) / (2 * (Real.pi : ℂ) * I * d) =
      (A / (2 * (Real.pi : ℂ) * d)) / I +
        (2 * (Real.pi : ℂ)) * (B / (2 * (Real.pi : ℂ) * d)) := by
  simp only [div_eq_mul_inv, mul_inv_rev, Complex.inv_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- The actual positive Poisson coefficient is the two normalized amplitude modes with the correct factors. -/
theorem positiveCoefficient_eq_secondModes {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (n : ℕ) :
    positiveCoefficient f g a b (n + 1) =
      secondModeTerm f (deriv g) a b n / I +
      (2 * (Real.pi : ℂ)) * secondModeTerm f (fun u => g u * deriv f u) a b n := by
  rw [positiveCoefficient, derivativeMode_eq_amplitude_integrals h]
  simp only [Nat.cast_add, Nat.cast_one, neg_mul, sub_neg_eq_add, secondModeTerm]
  exact amplitude_coefficient_normalize _ _ _

/-- The actual upper Poisson coefficient uses exactly the two modes above the same cutoff. -/
theorem negativeCoefficient_eq_upperModes {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (M n : ℕ) :
    negativeCoefficient f g a b (n + M + 1) =
      upperModeTerm f (deriv g) a b M n / I +
      (2 * (Real.pi : ℂ)) * upperModeTerm f (fun u => g u * deriv f u) a b M n := by
  rw [negativeCoefficient, derivativeMode_eq_amplitude_integrals h]
  simp only [Nat.cast_add, Nat.cast_one, upperModeTerm]
  exact amplitude_coefficient_normalize _ _ _

/-- Summing the actual positive coefficients retains both independently convergent amplitude series. -/
theorem tsum_positiveCoefficient_eq_secondModes {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b)
    (hg : Summable (secondModeTerm f (deriv g) a b))
    (hgf : Summable (secondModeTerm f (fun u => g u * deriv f u) a b)) :
    (∑' n : ℕ, positiveCoefficient f g a b n) =
      (∑' n : ℕ, secondModeTerm f (deriv g) a b n) / I +
        (2 * (Real.pi : ℂ)) * ∑' n : ℕ, secondModeTerm f (fun u => g u * deriv f u) a b n := by
  rw [(summable_positiveCoefficient h).tsum_eq_zero_add]
  simp only [positiveCoefficient, Nat.cast_zero, mul_zero, div_zero, zero_add]
  change (∑' n : ℕ, positiveCoefficient f g a b (n + 1)) = _
  simp_rw [positiveCoefficient_eq_secondModes h]
  rw [(hg.div_const I).tsum_add (hgf.mul_left _), tsum_div_const, tsum_mul_left]

/-- Summing the actual upper coefficients retains both amplitude series and their precise first frequency. -/
theorem tsum_negativeCoefficient_eq_upperModes {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (M : ℕ)
    (hg : Summable (upperModeTerm f (deriv g) a b M))
    (hgf : Summable (upperModeTerm f (fun u => g u * deriv f u) a b M)) :
    (∑' n : ℕ, negativeCoefficient f g a b (n + M + 1)) =
      (∑' n : ℕ, upperModeTerm f (deriv g) a b M n) / I +
        (2 * (Real.pi : ℂ)) * ∑' n : ℕ, upperModeTerm f (fun u => g u * deriv f u) a b M n := by
  simp_rw [negativeCoefficient_eq_upperModes h]
  rw [(hg.div_const I).tsum_add (hgf.mul_left _), tsum_div_const, tsum_mul_left]

/-- The exact Poisson remainder is assembled from the four actual second-integration amplitude series. -/
theorem weighted_sum_eq_second_mode_series {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (M : ℕ)
    (hgp : Summable (secondModeTerm f (deriv g) a b))
    (hgfp : Summable (secondModeTerm f (fun u => g u * deriv f u) a b))
    (hgn : Summable (upperModeTerm f (deriv g) a b M))
    (hgfn : Summable (upperModeTerm f (fun u => g u * deriv f u) a b M)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M =
      poissonHeadBoundary f g b M - poissonHeadBoundary f g a M +
        ((∑' n : ℕ, upperModeTerm f (deriv g) a b M n) / I +
          (2 * (Real.pi : ℂ)) * ∑' n : ℕ, upperModeTerm f (fun u => g u * deriv f u) a b M n) -
        ((∑' n : ℕ, secondModeTerm f (deriv g) a b n) / I +
          (2 * (Real.pi : ℂ)) * ∑' n : ℕ, secondModeTerm f (fun u => g u * deriv f u) a b n) +
        poissonBoundary f g a b := by
  rw [weighted_sum_eq_poissonMain_add_remainder h,
    tsum_negativeCoefficient_eq_upperModes h M hgn hgfn,
    tsum_positiveCoefficient_eq_secondModes h hgp hgfp]

/-- The actual AFE finite Poisson sum equals its four second-integration series, with every convergence input derived. -/
theorem afe_second_poisson_identity {σ c a b : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) :
    let f : ℝ → ℝ := afePhase c
    let g : ℝ → ℝ := afeWeight σ
    let M : ℕ := ⌊c / a⌋₊
    (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M =
      poissonHeadBoundary f g b M - poissonHeadBoundary f g a M +
        ((∑' n : ℕ, upperModeTerm f (deriv g) a b M n) / I +
          (2 * (Real.pi : ℂ)) * ∑' n : ℕ, upperModeTerm f (fun u => g u * deriv f u) a b M n) -
        ((∑' n : ℕ, secondModeTerm f (deriv g) a b n) / I +
          (2 * (Real.pi : ℂ)) * ∑' n : ℕ, secondModeTerm f (fun u => g u * deriv f u) a b n) +
        poissonBoundary f g a b := by
  exact weighted_sum_eq_second_mode_series (afe_partIRegularity hσ hc ha hab) ⌊c / a⌋₊
    (afe_positive_second_tail_bound hσ hc ha hab _ (Or.inl rfl)).1
    (afe_positive_second_tail_bound hσ hc ha hab _ (Or.inr rfl)).1
    (afe_upper_second_tail_bound hσ hc ha hab _ (Or.inl rfl) (Nat.lt_floor_add_one (c / a))).1
    (afe_upper_second_tail_bound hσ hc ha hab _ (Or.inr rfl) (Nat.lt_floor_add_one (c / a))).1

end DhimanKadiriQuesadaHerrera2026
