module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.PoissonShift
public import WeylPort.AFE.PowerWeights

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Actual constant and AFE weights as consumers of corrected Part I -/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory

/-- A constant weight satisfies the accepted hypotheses directly, including its zero derivatives. -/
theorem constant_weight_partIRegularity {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hfp : ∀ x ∈ Set.Icc a b, 0 < deriv f x) (hfa : AntitoneOn (deriv f) (Set.Icc a b)) :
    PartIRegularity f (fun _ => 1) a b := by
  refine ⟨hab, hfd, hfc, hfp, hfa, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x _
    fun_prop
  · have hd : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => 0 := by
      funext x
      simp only [deriv_const]
    rw [hd]
    exact continuousOn_const
  · intro x _
    norm_num
  · intro x _ y _ _
    exact le_rfl
  · intro x _ y _ _
    simp only [deriv_const, abs_zero, le_refl]
  · intro x _ y _ _
    simp only [deriv_const, abs_zero, zero_div, le_refl]

/-- Corollary 0.1 Part I, with the complete printed error and genuine constant weight. -/
theorem corollary_poisson_partI {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hfp : ∀ x ∈ Set.Icc a b, 0 < deriv f x) (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, Complex.exp (2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 ⌊deriv f a⌋₊,
        ∫ x in a..b, Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      (1 / Real.pi) * (Real.log (1 + deriv f a) + Real.log (1 + (⌊deriv f a⌋₊ : ℝ)) +
        Real.eulerMascheroniConstant - 1 / (2 * (1 + (⌊deriv f a⌋₊ : ℝ))) -
        1 / (2 * (1 + deriv f a)) - (Complex.digamma ((1 - Int.fract (deriv f a) : ℝ) : ℂ)).re +
        Real.log 2 + 1 / deriv f a) := by
  have he := corrected_poisson_partI_zero_half_integer
    (constant_weight_partIRegularity hab hfd hfc hfp hfa.antitoneOn) ha hb
  simp only [weightedWave, poissonMain_eq_source, Complex.ofReal_one, one_mul] at he
  apply he.trans_eq
  have hy := hfp a (Set.left_mem_Icc.mpr hab.le)
  have hδ := shifted_floor_delta (N := 0) (y := deriv f a) (by simpa only [Nat.cast_zero] using hy.le)
  simp only [Nat.sub_zero, Nat.cast_zero, sub_zero] at hδ
  unfold partIAnalyticError partICoefficient
  simp only [deriv_const, abs_zero, zero_add, mul_one]
  rw [hδ, add_comm (⌊deriv f a⌋₊ : ℝ) 1]
  field_simp
  ring

/-- The actual AFE weights satisfy every regularity hypothesis of corrected Part I, including σ=0. -/
theorem afe_partIRegularity {sigma c a b : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) : PartIRegularity (afePhase c) (afeWeight sigma) a b := by
  have hx (x : ℝ) (hxi : x ∈ Set.Icc a b) : 0 < x := ha.trans_le hxi.1
  have hdf (x : ℝ) (hxi : x ∈ Set.Icc a b) : deriv (afePhase c) x = c / x :=
    (afePhase_hasDerivAt c (hx x hxi)).deriv
  have hdg (x : ℝ) (hxi : x ∈ Set.Icc a b) :
      deriv (afeWeight sigma) x = -sigma * x ^ (-sigma - 1) :=
    (afeWeight_hasDerivAt sigma (hx x hxi)).deriv
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun x hxi => hx x hxi
  refine ⟨hab, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hxi
    exact (afePhase_hasDerivAt c (hx x hxi)).differentiableAt
  · have hd : ContinuousOn (fun x => c / x) (Set.Icc a b) :=
      continuousOn_const.div continuousOn_id (fun x hxi => (hx x hxi).ne')
    exact hd.congr hdf
  · intro x hxi
    rw [hdf x hxi]
    exact div_pos hc (hx x hxi)
  · intro x hxi y hyi hxy
    rw [hdf x hxi, hdf y hyi]
    exact div_le_div_of_nonneg_left hc.le (hx x hxi) hxy
  · intro x hxi
    exact (afeWeight_hasDerivAt sigma (hx x hxi)).differentiableAt
  · have hd : ContinuousOn (fun x => -sigma * x ^ (-sigma - 1)) (Set.Icc a b) :=
      continuousOn_const.mul (continuousOn_id.rpow_const (fun x hxi => Or.inl (hx x hxi).ne'))
    exact hd.congr hdg
  · intro x hxi
    exact (afeWeight_pos sigma (hx x hxi)).le
  · exact (afeWeight_antitone hsigma).mono hsub
  · exact (abs_deriv_afeWeight_antitone hsigma).mono hsub
  · exact (afe_derivative_quotient_antitone hsigma hc.le).mono hsub

/-- The completed Poisson theorem is actually applied to the power weight and logarithmic phase. -/
theorem afe_finite_poisson_partI {sigma c a b : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, ((n : ℝ) ^ (-sigma) : ℝ) *
        Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log (n : ℝ) : ℝ) : ℂ))) -
      ∑ ν ∈ Finset.Icc 0 ⌊c / a⌋₊,
        ∫ x in a..b, (x ^ (-sigma) : ℝ) *
          Complex.exp (2 * Real.pi * Complex.I * ((c * Real.log x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      partIZeroError (afePhase c) (afeWeight sigma) a b := by
  have he := corrected_poisson_partI_zero (afe_partIRegularity hsigma hc ha hab)
  rw [poissonMain_eq_source, (afePhase_hasDerivAt c ha).deriv] at he
  simpa only [weightedWave, afeWeight, afePhase] using he


/-- The finite endpoint sum is empty whenever the derivative cutoff is below one. -/
theorem poissonEndpointMajorant_eq_zero {y : ℝ} (hy : y < 1) (x : ℝ) :
    poissonEndpointMajorant x y = 0 := by
  classical
  simp [poissonEndpointMajorant, Nat.floor_eq_zero.mpr hy, tildeS1, not_le.mpr hy]

/-- The exact logarithmic/digamma factor appearing in the first AFE constant. -/
noncomputable def afePartIFactor (u : ℝ) : ℝ :=
  Real.log (1 + u) + Real.eulerMascheroniConstant - (Complex.digamma ((1 - u : ℝ) : ℂ)).re -
    1 / (2 * (1 + u)) - 1 / 2

/-- The actual analytic Poisson error for the AFE weight below the first frequency. -/
theorem afe_partIAnalyticError_eq {sigma c a : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 < c)
    (ha : 0 < a) (hca : c < a) :
    partIAnalyticError (afePhase c) (afeWeight sigma) a =
      a ^ (-sigma) / Real.pi * (1 + sigma / (2 * Real.pi * c)) * afePartIFactor (c / a) := by
  have hcut : ⌊c / a⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one ha).mpr hca)
  unfold partIAnalyticError partICoefficient
  rw [(afePhase_hasDerivAt c ha).deriv, abs_deriv_afeWeight hsigma ha, hcut]
  simp only [Nat.cast_zero, zero_add, Real.log_one, add_zero, afeWeight]
  rw [Real.rpow_sub_one ha.ne']
  unfold afePartIFactor
  field_simp
  ring

/-- With an empty Fourier head, the complete AFE error retains only its actual complex boundary. -/
theorem afe_partIZeroError_eq {sigma c a b : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 < c)
    (ha : 0 < a) (hca : c < a) :
    partIZeroError (afePhase c) (afeWeight sigma) a b =
      a ^ (-sigma) / Real.pi * (1 + sigma / (2 * Real.pi * c)) * afePartIFactor (c / a) +
        ‖poissonBoundary (afePhase c) (afeWeight sigma) a b‖ := by
  unfold partIZeroError
  rw [afe_partIAnalyticError_eq hsigma hc ha hca, (afePhase_hasDerivAt c ha).deriv,
    poissonEndpointMajorant_eq_zero ((div_lt_one ha).mpr hca),
    poissonEndpointMajorant_eq_zero ((div_lt_one ha).mpr hca)]
  simp only [mul_zero, add_zero, zero_div]

/-- A half-integer left endpoint removes its boundary term exactly. -/
theorem norm_poissonBoundary_left_half_integer_le {f g : ℝ → ℝ} {a b : ℝ}
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : 0 ≤ g b) :
    ‖poissonBoundary f g a b‖ ≤ g b / 2 := by
  obtain ⟨k, rfl⟩ := ha
  have hf : Int.fract ((k : ℝ) + 1 / 2) = (1 / 2 : ℝ) := by
    rw [Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr (by norm_num)
  rw [poissonBoundary, hf, sub_self, Complex.ofReal_zero, mul_zero, zero_sub, norm_neg,
    norm_mul, norm_weightedWave hb, Complex.norm_real, Real.norm_eq_abs]
  simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left (abs_fract_sub_half_le b) hb

/-- Below the first frequency, corrected Part I supplies the finite AFE comparison with a vanishing
right-endpoint error; the full zeta limit is a separate obligation. -/
theorem afe_finite_sum_sub_integral_bound {sigma c a b : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) (hca : c < a)
    (hahalf : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave (afePhase c) (afeWeight sigma) (n : ℝ)) -
      ∫ x in a..b, weightedWave (afePhase c) (afeWeight sigma) x‖ ≤
      a ^ (-sigma) / Real.pi * (1 + sigma / (2 * Real.pi * c)) * afePartIFactor (c / a) +
        b ^ (-sigma) / 2 := by
  have he := corrected_poisson_partI_zero (afe_partIRegularity hsigma hc ha hab)
  have hcut : ⌊c / a⌋₊ = 0 := Nat.floor_eq_zero.mpr ((div_lt_one ha).mpr hca)
  rw [(afePhase_hasDerivAt c ha).deriv, hcut, poissonMain] at he
  simp only [Finset.Icc_self, Finset.sum_singleton, expMode, Nat.cast_zero, mul_zero,
    zero_mul, Complex.ofReal_zero, Complex.exp_zero, mul_one] at he
  rw [afe_partIZeroError_eq hsigma hc ha hca] at he
  exact he.trans (add_le_add le_rfl
    (norm_poissonBoundary_left_half_integer_le hahalf (afeWeight_pos sigma (ha.trans hab)).le))


/-- The AFE error factor is nonnegative by the actual convergent harmonic-tail bounds. -/
theorem afePartIFactor_nonneg {u : ℝ} (hu : 0 < u) (hu1 : u < 1) : 0 ≤ afePartIFactor u := by
  have ht := (harmonic_tail_bounds (N := 0) hu (by simpa only [Nat.cast_zero, zero_add] using hu1)).2
  simp only [Nat.cast_zero, add_zero, zero_add, Real.log_one, zero_div, sub_zero, mul_one] at ht
  have htn : 0 ≤ ∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 - u)) := by
    apply tsum_nonneg
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hd : 0 < (n : ℝ) + 1 - u := by linarith
    positivity
  have hp := harmonic_plus_bound hu
  have hpn : 0 ≤ ∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + u)) := by
    apply tsum_nonneg
    intro n
    positivity
  have he := mul_nonneg hu.le (add_nonneg (htn.trans ht) (hpn.trans hp))
  convert he using 1
  unfold afePartIFactor
  rw [add_comm u 1]
  field_simp
  ring

end DhimanKadiriQuesadaHerrera2026
