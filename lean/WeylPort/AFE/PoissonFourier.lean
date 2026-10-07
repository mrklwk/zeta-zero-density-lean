module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.NonstationaryPhase
public import WeylPort.AFE.AbelSawtooth

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Absolute convergence of the actual Poisson Fourier integrals

The hypotheses below contain only the differentiability, sign, and monotonicity
conditions of the accepted Part I repair. No Fourier identity or remainder
estimate is assumed.
-/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory Filter
open scoped Topology

/-- Analytic hypotheses for the repaired N = 0 Part I, allowing a zero weight. -/
structure PartIRegularity (f g : ℝ → ℝ) (a b : ℝ) : Prop where
  lt : a < b
  f_differentiable : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x
  f_deriv_continuous : ContinuousOn (deriv f) (Set.Icc a b)
  f_deriv_pos : ∀ x ∈ Set.Icc a b, 0 < deriv f x
  f_deriv_antitone : AntitoneOn (deriv f) (Set.Icc a b)
  g_differentiable : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ g x
  g_deriv_continuous : ContinuousOn (deriv g) (Set.Icc a b)
  g_nonneg : ∀ x ∈ Set.Icc a b, 0 ≤ g x
  g_antitone : AntitoneOn g (Set.Icc a b)
  g_abs_deriv_antitone : AntitoneOn (fun x => |deriv g x|) (Set.Icc a b)
  g_quotient_antitone : AntitoneOn (fun x => |deriv g x| / (1 + deriv f x)) (Set.Icc a b)

/-- The actual weighted exponential in the source sum. -/
noncomputable def weightedWave (f g : ℝ → ℝ) (x : ℝ) : ℂ :=
  (g x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f x : ℂ))

/-- The explicit derivative amplitude before a frequency shift. -/
noncomputable def waveDerivative (f g : ℝ → ℝ) (x : ℝ) : ℂ :=
  (((deriv g x : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((g x * deriv f x : ℝ) : ℂ)) *
    Complex.exp (2 * Real.pi * Complex.I * (f x : ℂ))

/-- The actual positive or negative frequency integral of the derivative amplitude. -/
noncomputable def derivativeMode (f g : ℝ → ℝ) (a b ν : ℝ) : ℂ :=
  ∫ x in a..b, (((deriv g x : ℝ) : ℂ) + 2 * Real.pi * Complex.I *
    ((g x * deriv f x : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((f x - ν * x : ℝ) : ℂ))

/-- The negative-sign Fourier coefficient in S₁, including the zero term as zero. -/
noncomputable def negativeCoefficient (f g : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℂ :=
  derivativeMode f g a b n / (2 * Real.pi * Complex.I * n)

/-- The positive-sign Fourier coefficient in S₂, including the zero term as zero. -/
noncomputable def positiveCoefficient (f g : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℂ :=
  derivativeMode f g a b (-(n : ℝ)) / (2 * Real.pi * Complex.I * n)

/-- The shared source numerator divided by 2π². -/
noncomputable def partICoefficient (f g : ℝ → ℝ) (a : ℝ) : ℝ :=
  (|deriv g a| + 2 * Real.pi * g a * deriv f a) / (2 * Real.pi ^ 2)

/-- The explicit amplitude is the derivative of the actual source wave. -/
theorem waveDerivative_eq_deriv {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    waveDerivative f g x = deriv (weightedWave f g) x := by
  unfold weightedWave
  rw [(weighted_wave_hasDerivAt hf hg).deriv]
  simp only [waveDerivative, Complex.ofReal_mul, mul_assoc]

/-- The weight is continuous under the source's differentiability hypothesis. -/
theorem PartIRegularity.g_continuous {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) : ContinuousOn g (Set.Icc a b) :=
  fun x hx => (h.g_differentiable x hx).continuousAt.continuousWithinAt

/-- The phase is continuous under the source's differentiability hypothesis. -/
theorem PartIRegularity.f_continuous {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) : ContinuousOn f (Set.Icc a b) :=
  fun x hx => (h.f_differentiable x hx).continuousAt.continuousWithinAt

/-- The shared coefficient in the two absolute tail majorants is nonnegative. -/
theorem PartIRegularity.coefficient_nonneg {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) : 0 ≤ partICoefficient f g a := by
  have ha := Set.left_mem_Icc.mpr h.lt.le
  have hga := h.g_nonneg a ha
  have hfa := h.f_deriv_pos a ha
  unfold partICoefficient
  positivity

/-- The upper-frequency integral coefficient has the exact mixed harmonic majorant. -/
theorem negativeCoefficient_bound {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) {n : ℕ} (hn : deriv f a < n) :
    ‖negativeCoefficient f g a b n‖ ≤
      partICoefficient f g a * (1 / ((n : ℝ) * ((n : ℝ) - deriv f a))) := by
  have hi := negative_derivative_amplitude_integral_bound h.lt f g h.f_differentiable
    h.f_deriv_continuous (fun x hx => (h.f_deriv_pos x hx).le) h.f_deriv_antitone
    h.g_continuous h.g_deriv_continuous h.g_nonneg h.g_antitone h.g_abs_deriv_antitone hn
  rw [negativeCoefficient, norm_div]
  have hd : ‖(2 * Real.pi * Complex.I * n : ℂ)‖ = 2 * Real.pi * n := by
    simp
  rw [hd]
  have hc := div_le_div_of_nonneg_right hi (by positivity : 0 ≤ 2 * Real.pi * (n : ℝ))
  convert hc using 1
  all_goals simp only [partICoefficient, derivativeMode, div_eq_mul_inv, mul_inv_rev] <;> ring

/-- The lower-frequency integral coefficient has the exact positive harmonic majorant. -/
theorem positiveCoefficient_bound {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) {n : ℕ} (hn : 1 ≤ n) :
    ‖positiveCoefficient f g a b n‖ ≤
      partICoefficient f g a * (1 / ((n : ℝ) * ((n : ℝ) + deriv f a))) := by
  have hi := positive_derivative_amplitude_integral_bound h.lt f g h.f_differentiable
    h.f_deriv_continuous (fun x hx => (h.f_deriv_pos x hx).le) h.f_deriv_antitone
    h.g_continuous h.g_deriv_continuous h.g_nonneg h.g_antitone h.g_quotient_antitone
    (by exact_mod_cast hn : (1 : ℝ) ≤ n)
  have he : derivativeMode f g a b (-(n : ℝ)) =
      ∫ x in a..b, (((deriv g x : ℝ) : ℂ) + 2 * Real.pi * Complex.I *
        ((g x * deriv f x : ℝ) : ℂ)) *
          Complex.exp (2 * Real.pi * Complex.I * ((f x + (n : ℝ) * x : ℝ) : ℂ)) := by
    simp [derivativeMode]
  rw [positiveCoefficient, he, norm_div]
  have hd : ‖(2 * Real.pi * Complex.I * n : ℂ)‖ = 2 * Real.pi * n := by
    simp
  rw [hd]
  have hc := div_le_div_of_nonneg_right hi (by positivity : 0 ≤ 2 * Real.pi * (n : ℝ))
  convert hc using 1
  unfold partICoefficient
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring


/-- Every nonstationary upper-frequency tail is absolutely summable. -/
theorem summable_negativeCoefficient_tail {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) {N : ℕ} (hN : deriv f a < (N : ℝ) + 1) :
    Summable (fun n : ℕ => negativeCoefficient f g a b (n + N + 1)) := by
  have hy := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  apply ((hasSum_harmonic_tail hy hN).summable.mul_left (partICoefficient f g a)).of_norm_bounded
  intro n
  have hn : deriv f a < ((n + N + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  simpa only [Nat.cast_add, Nat.cast_one] using negativeCoefficient_bound h hn

/-- The stationary frequencies form only a finite head, so S₁ converges absolutely. -/
theorem summable_negativeCoefficient {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) : Summable (negativeCoefficient f g a b) := by
  have ht := summable_negativeCoefficient_tail h (Nat.lt_floor_add_one (deriv f a))
  apply (summable_nat_add_iff (⌊deriv f a⌋₊ + 1)).mp
  simpa only [Nat.add_assoc] using ht

/-- Every positive frequency belongs to the absolutely convergent S₂ tail. -/
theorem summable_positiveCoefficient {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) : Summable (positiveCoefficient f g a b) := by
  have hy := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  apply (summable_nat_add_iff 1).mp
  apply ((hasSum_harmonic_plus hy).summable.mul_left (partICoefficient f g a)).of_norm_bounded
  intro n
  simpa only [Nat.cast_add, Nat.cast_one] using positiveCoefficient_bound h (Nat.le_add_left 1 n)

/-- The explicit source derivative amplitude is continuous on the closed interval. -/
theorem PartIRegularity.waveDerivative_continuous {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) : ContinuousOn (waveDerivative f g) (Set.Icc a b) := by
  unfold waveDerivative
  exact ((Complex.continuous_ofReal.comp_continuousOn h.g_deriv_continuous).add
    (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (h.g_continuous.mul h.f_deriv_continuous)))).mul
    ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn h.f_continuous)).cexp)

/-- The Fourier shift acts on the actual derivative amplitude by subtracting νx from the phase. -/
theorem waveDerivative_mul_phase (f g : ℝ → ℝ) (x ν : ℝ) :
    waveDerivative f g x * Complex.exp (-2 * Real.pi * Complex.I * (ν : ℂ) * (x : ℂ)) =
      (((deriv g x : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((g x * deriv f x : ℝ) : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * ((f x - ν * x : ℝ) : ℂ)) := by
  unfold waveDerivative
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Integration of the negative Fourier product gives the source's literal integral. -/
theorem integral_waveDerivative_expMode (f g : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    (∫ x in a..b, waveDerivative f g x * expMode x n) = derivativeMode f g a b n := by
  unfold derivativeMode
  apply intervalIntegral.integral_congr
  intro x _
  have he : expMode x n = Complex.exp (-2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ)) := by
    unfold expMode
    congr 1
    push_cast
    ring
  dsimp only
  rw [he]
  simpa only [Complex.ofReal_natCast] using waveDerivative_mul_phase f g x (n : ℝ)

/-- Integration of the positive Fourier product gives the source's literal integral. -/
theorem integral_waveDerivative_expMode_neg (f g : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    (∫ x in a..b, waveDerivative f g x * expMode (-x) n) =
      derivativeMode f g a b (-(n : ℝ)) := by
  unfold derivativeMode
  apply intervalIntegral.integral_congr
  intro x _
  have he : expMode (-x) n = Complex.exp (-2 * Real.pi * Complex.I * (-(n : ℝ) : ℝ) * (x : ℂ)) := by
    unfold expMode
    congr 1
    push_cast
    ring
  dsimp only
  rw [he, waveDerivative_mul_phase]

/-- The two integrals S₁ and S₂ are precisely the paired sawtooth integral coefficients. -/
theorem integral_waveDerivative_sawtoothMode {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (n : ℕ) :
    (∫ x in a..b, waveDerivative f g x * sawtoothMode n x) =
      negativeCoefficient f g a b n - positiveCoefficient f g a b n := by
  have hi (u : ℝ → ℂ) (hu : Continuous u) :
      IntervalIntegrable (fun x => waveDerivative f g x * u x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h.lt.le]
    exact h.waveDerivative_continuous.mul hu.continuousOn
  have hn : Continuous (fun x => expMode x n) := by unfold expMode; fun_prop
  have hp : Continuous (fun x => expMode (-x) n) := by unfold expMode; fun_prop
  simp only [sawtoothMode, ← mul_div_assoc, mul_sub]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (hi _ hn) (hi _ hp),
    integral_waveDerivative_expMode, integral_waveDerivative_expMode_neg, sub_div]
  rfl

/-- The Fourier series may be integrated for every amplitude satisfying the repaired hypotheses. -/
theorem integral_waveDerivative_sawtooth {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) :
    (∫ x in a..b, waveDerivative f g x * ((Int.fract x - 1 / 2 : ℝ) : ℂ)) =
      (∑' n, negativeCoefficient f g a b n) - ∑' n, positiveCoefficient f g a b n := by
  have hi : Integrable (waveDerivative f g) (volume.restrict (Set.Ioc a b)) :=
    h.waveDerivative_continuous.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hs : Summable (fun n : ℕ => ∫ x in Set.Ioc a b, waveDerivative f g x * sawtoothMode n x) := by
    simp_rw [← intervalIntegral.integral_of_le h.lt.le, integral_waveDerivative_sawtoothMode h]
    exact (summable_negativeCoefficient h).sub (summable_positiveCoefficient h)
  have he := integral_mul_sawtooth_eq_tsum hi hs
  rw [← intervalIntegral.integral_of_le h.lt.le] at he
  simp_rw [← intervalIntegral.integral_of_le h.lt.le, integral_waveDerivative_sawtoothMode h] at he
  rw [he, (summable_negativeCoefficient h).tsum_sub (summable_positiveCoefficient h)]


/-- The complete S₁ tail has the exact digamma majorant before the logarithmic relaxation. -/
theorem norm_negativeCoefficient_tail_le_digamma {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) {N : ℕ} (hN : deriv f a < (N : ℝ) + 1) :
    ‖∑' n : ℕ, negativeCoefficient f g a b (n + N + 1)‖ ≤
      partICoefficient f g a *
        (((Complex.digamma ((N : ℝ) + 1 : ℝ)).re -
          (Complex.digamma ((N : ℝ) + 1 - deriv f a : ℝ)).re) / deriv f a) := by
  have hy := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  apply tsum_of_norm_bounded ((hasSum_harmonic_tail hy hN).mul_left (partICoefficient f g a))
  intro n
  have hn : deriv f a < ((n + N + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) n]
  simpa only [Nat.cast_add, Nat.cast_one] using negativeCoefficient_bound h hn

/-- The complete S₂ sum has the exact digamma majorant, with no omitted zero-frequency term. -/
theorem norm_positiveCoefficient_sum_le_digamma {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) :
    ‖∑' n : ℕ, positiveCoefficient f g a b n‖ ≤
      partICoefficient f g a *
        (((Complex.digamma (deriv f a + 1 : ℝ)).re + Real.eulerMascheroniConstant) / deriv f a) := by
  have hy := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  rw [(summable_positiveCoefficient h).tsum_eq_zero_add]
  simp only [positiveCoefficient, Nat.cast_zero, mul_zero, div_zero, zero_add]
  change ‖∑' n : ℕ, positiveCoefficient f g a b (n + 1)‖ ≤ _
  apply tsum_of_norm_bounded ((hasSum_harmonic_plus hy).mul_left (partICoefficient f g a))
  intro n
  simpa only [Nat.cast_add, Nat.cast_one] using positiveCoefficient_bound h (Nat.le_add_left 1 n)

/-- The source's logarithmic S₁ bound keeps its negative half-reciprocal correction. -/
theorem norm_negativeCoefficient_tail_le_source {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) {N : ℕ} (hN : deriv f a < (N : ℝ) + 1) :
    ‖∑' n : ℕ, negativeCoefficient f g a b (n + N + 1)‖ ≤
      (partICoefficient f g a / deriv f a) *
        (Real.log ((N : ℝ) + 1) - 1 / (2 * ((N : ℝ) + 1)) -
          (Complex.digamma ((N : ℝ) + 1 - deriv f a : ℝ)).re) := by
  have hy := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  have hd := (real_digamma_bounds (by positivity : 0 < (N : ℝ) + 1)).2
  have hb := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (sub_le_sub_right hd
      (Complex.digamma ((N : ℝ) + 1 - deriv f a : ℝ)).re) hy.le) h.coefficient_nonneg
  exact (norm_negativeCoefficient_tail_le_digamma h hN).trans (by
    convert hb using 1
    ring)

/-- The source's logarithmic S₂ bound keeps its negative half-reciprocal correction. -/
theorem norm_positiveCoefficient_sum_le_source {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) :
    ‖∑' n : ℕ, positiveCoefficient f g a b n‖ ≤
      (partICoefficient f g a / deriv f a) *
        (Real.eulerMascheroniConstant + Real.log (1 + deriv f a) -
          1 / (2 * (1 + deriv f a))) := by
  have hy := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  have hd := (real_digamma_bounds (by linarith : 0 < deriv f a + 1)).2
  have hb := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (add_le_add_right hd Real.eulerMascheroniConstant) hy.le)
    h.coefficient_nonneg
  exact (norm_positiveCoefficient_sum_le_digamma h).trans (by
    rw [add_comm (deriv f a) 1] at hb
    convert hb using 1
    · rw [add_comm (deriv f a) 1]
      ring
    · ring)

end DhimanKadiriQuesadaHerrera2026
