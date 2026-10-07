module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.ExponentialTails
public import WeylPort.Analytic.NonstationaryFoundation

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Frequency-tail integral estimates for the corrected Poisson theorem

This module consumes the existing node-71 nonstationary phase proof directly.
It does not copy the completed foundation or assume a Poisson remainder bound.
-/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory

/-- The existing first-derivative test in the source's interval-integral convention. -/
theorem nonstationary_interval_bound {a b : ℝ} (hab : a < b) (φ h : ℝ → ℝ)
    (hφ : ContDiffOn ℝ 1 φ (Set.Icc a b))
    (hφ' : ∀ x ∈ Set.Icc a b, deriv φ x ≠ 0)
    (hc : ContinuousOn (fun x => h x / deriv φ x) (Set.Icc a b))
    (ha : AntitoneOn (fun x => |h x / deriv φ x|) (Set.Icc a b)) :
    ‖∫ x in a..b, (h x : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (φ x : ℂ))‖ ≤
      |h a / deriv φ a| / Real.pi := by
  have ht := ZetaAppendix.nonstationary_phase_integral_bound hab φ hφ hφ'
    h (fun x => h x / deriv φ x) (fun _ => rfl) hc ha
  simpa only [intervalIntegral.integral_of_le hab.le, integral_Icc_eq_integral_Ioc] using ht

/-- The derivative of the actual frequency-shifted phase at every regular point. -/
theorem deriv_frequency_shift {f : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (ν : ℝ) :
    deriv (fun u => f u - ν * u) x = deriv f x - ν := by
  simpa using (hf.hasDerivAt.fun_sub ((hasDerivAt_id x).const_mul ν)).deriv

/-- Above the initial slope, every shifted phase derivative is strictly negative. -/
theorem frequency_shift_deriv_neg {a b ν : ℝ} {f : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hanti : AntitoneOn (deriv f) (Set.Icc a b)) (hν : deriv f a < ν)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    deriv (fun u => f u - ν * u) x < 0 := by
  rw [deriv_frequency_shift (hf x hx)]
  have h := hanti (Set.left_mem_Icc.mpr (hx.1.trans hx.2)) hx hx.1
  linarith

/-- The decreasing absolute-amplitude hypothesis supplies the negative-tail quotient test. -/
theorem negative_frequency_quotient_antitone {a b ν : ℝ} {f h : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfanti : AntitoneOn (deriv f) (Set.Icc a b))
    (hhanti : AntitoneOn (fun x => |h x|) (Set.Icc a b)) (hν : deriv f a < ν) :
    AntitoneOn (fun x => |h x / deriv (fun u => f u - ν * u) x|) (Set.Icc a b) := by
  intro x hx y hy hxy
  dsimp only
  have hxneg := frequency_shift_deriv_neg hf hfanti hν hx
  have hyneg := frequency_shift_deriv_neg hf hfanti hν hy
  rw [abs_div, abs_div, abs_of_neg hyneg, abs_of_neg hxneg,
    deriv_frequency_shift (hf x hx), deriv_frequency_shift (hf y hy)]
  simp only [neg_sub]
  have hxpos : 0 < ν - deriv f x := by
    rw [deriv_frequency_shift (hf x hx)] at hxneg
    linarith
  exact div_le_div₀ (abs_nonneg _) (hhanti hx hy hxy) hxpos (by linarith [hfanti hx hy hxy])

/-- The actual negative-frequency integral has the sharp first-derivative constant. -/
theorem negative_frequency_integral_bound {a b ν : ℝ} (hab : a < b) (f h : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Icc a b))
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hhc : ContinuousOn h (Set.Icc a b))
    (hha : AntitoneOn (fun x => |h x|) (Set.Icc a b)) (hν : deriv f a < ν) :
    ‖∫ x in a..b, (h x : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((f x - ν * x : ℝ) : ℂ))‖ ≤
        |h a| / (Real.pi * (ν - deriv f a)) := by
  have hneg {x : ℝ} (hx : x ∈ Set.Icc a b) :
      deriv (fun u => f u - ν * u) x < 0 := frequency_shift_deriv_neg hfd hfa hν hx
  have hc : ContinuousOn (fun x => h x / deriv (fun u => f u - ν * u) x) (Set.Icc a b) := by
    have hdcont : ContinuousOn (fun x => deriv f x - ν) (Set.Icc a b) :=
      hfc.sub continuousOn_const
    have hnz (x : ℝ) (hx : x ∈ Set.Icc a b) : deriv f x - ν ≠ 0 := by
      have ht := hneg hx
      rw [deriv_frequency_shift (hfd x hx)] at ht
      exact ht.ne
    apply (hhc.div hdcont hnz).congr
    intro x hx
    dsimp only [Pi.div_apply]
    rw [deriv_frequency_shift (hfd x hx)]
  have ht := nonstationary_interval_bound hab (fun x => f x - ν * x) h
    (hf.sub (contDiffOn_const.mul contDiffOn_id)) (fun x hx => (hneg hx).ne) hc
    (negative_frequency_quotient_antitone hfd hfa hha hν)
  rw [abs_div, abs_of_neg (hneg (Set.left_mem_Icc.mpr hab.le)),
    deriv_frequency_shift (hfd a (Set.left_mem_Icc.mpr hab.le)), neg_sub] at ht
  simpa only [div_div, mul_comm] using ht

/-- The accepted first positive-frequency quotient controls every larger positive frequency. -/
theorem positive_frequency_quotient_antitone {s : Set ℝ} {p h : ℝ → ℝ} {ν : ℝ}
    (hp : ∀ x ∈ s, 0 ≤ p x) (hpa : AntitoneOn p s)
    (hh : AntitoneOn (fun x => |h x| / (1 + p x)) s) (hν : 1 ≤ ν) :
    AntitoneOn (fun x => |h x| / (ν + p x)) s := by
  intro x hx y hy hxy
  dsimp only
  have hpx := hp x hx
  have hpy := hp y hy
  have hpxy := hpa hx hy hxy
  have hratio : (1 + p y) / (ν + p y) ≤ (1 + p x) / (ν + p x) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [mul_nonneg (by linarith : 0 ≤ ν - 1) (sub_nonneg.mpr hpxy)]
  have he (u : ℝ) (hu : u ∈ s) :
      |h u| / (ν + p u) = (|h u| / (1 + p u)) * ((1 + p u) / (ν + p u)) := by
    have hpu := hp u hu
    have hden : 1 + p u ≠ 0 := by positivity
    field_simp
  rw [he x hx, he y hy]
  exact mul_le_mul (hh hx hy hxy) hratio (by positivity) (by positivity)

/-- A nonnegative decreasing weight times the slope satisfies the accepted quotient condition. -/
theorem weighted_slope_quotient_antitone {s : Set ℝ} {g p : ℝ → ℝ}
    (hg : ∀ x ∈ s, 0 ≤ g x) (hp : ∀ x ∈ s, 0 ≤ p x)
    (hga : AntitoneOn g s) (hpa : AntitoneOn p s) :
    AntitoneOn (fun x => |g x * p x| / (1 + p x)) s := by
  intro x hx y hy hxy
  dsimp only
  have hgx := hg x hx
  have hgy := hg y hy
  have hpx := hp x hx
  have hpy := hp y hy
  rw [abs_of_nonneg (mul_nonneg hgy hpy), abs_of_nonneg (mul_nonneg hgx hpx),
    mul_div_assoc, mul_div_assoc]
  apply mul_le_mul (hga hx hy hxy) _ (by positivity) hgx
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [hpa hx hy hxy]

/-- The same weighted slope has decreasing absolute value for the negative-frequency tail. -/
theorem weighted_slope_abs_antitone {s : Set ℝ} {g p : ℝ → ℝ}
    (hg : ∀ x ∈ s, 0 ≤ g x) (hp : ∀ x ∈ s, 0 ≤ p x)
    (hga : AntitoneOn g s) (hpa : AntitoneOn p s) :
    AntitoneOn (fun x => |g x * p x|) s := by
  intro x hx y hy hxy
  dsimp only
  rw [abs_of_nonneg (mul_nonneg (hg y hy) (hp y hy)),
    abs_of_nonneg (mul_nonneg (hg x hx) (hp x hx))]
  exact mul_le_mul (hga hx hy hxy) (hpa hx hy hxy) (hp y hy) (hg x hx)

/-- The actual positive-frequency integral uses the quotient condition. -/
theorem positive_frequency_integral_bound {a b ν : ℝ} (hab : a < b) (f h : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.Icc a b))
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hfp : ∀ x ∈ Set.Icc a b, 0 ≤ deriv f x)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hhc : ContinuousOn h (Set.Icc a b))
    (hha : AntitoneOn (fun x => |h x| / (1 + deriv f x)) (Set.Icc a b)) (hν : 1 ≤ ν) :
    ‖∫ x in a..b, (h x : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * ((f x + ν * x : ℝ) : ℂ))‖ ≤
        |h a| / (Real.pi * (ν + deriv f a)) := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) :
      deriv (fun u => f u + ν * u) x = deriv f x + ν := by
    simpa using ((hfd x hx).hasDerivAt.fun_add ((hasDerivAt_id x).const_mul ν)).deriv
  have hpos (x : ℝ) (hx : x ∈ Set.Icc a b) :
      0 < deriv (fun u => f u + ν * u) x := by
    rw [hd x hx]
    linarith [hfp x hx]
  have hc : ContinuousOn (fun x => h x / deriv (fun u => f u + ν * u) x) (Set.Icc a b) := by
    have hdcont : ContinuousOn (fun x => deriv f x + ν) (Set.Icc a b) :=
      hfc.add continuousOn_const
    have hnz (x : ℝ) (hx : x ∈ Set.Icc a b) : deriv f x + ν ≠ 0 := by
      have ht := hpos x hx
      rw [hd x hx] at ht
      exact ht.ne'
    apply (hhc.div hdcont hnz).congr
    intro x hx
    dsimp only [Pi.div_apply]
    rw [hd x hx]
  have ha : AntitoneOn (fun x => |h x / deriv (fun u => f u + ν * u) x|) (Set.Icc a b) := by
    intro x hx y hy hxy
    dsimp only
    rw [abs_div, abs_div, abs_of_pos (hpos y hy), abs_of_pos (hpos x hx), hd x hx, hd y hy]
    simpa only [add_comm] using (positive_frequency_quotient_antitone hfp hfa hha hν hx hy hxy)
  have ht := nonstationary_interval_bound hab (fun x => f x + ν * x) h
    (hf.add (contDiffOn_const.mul contDiffOn_id)) (fun x hx => (hpos x hx).ne') hc ha
  rw [abs_div, abs_of_pos (hpos a (Set.left_mem_Icc.mpr hab.le)),
    hd a (Set.left_mem_Icc.mpr hab.le)] at ht
  simpa only [div_div, mul_comm, add_comm] using ht

/-- The source's differentiable phase with continuous derivative is C¹ on the interval. -/
theorem contDiffOn_one_of_continuous_deriv {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hc : ContinuousOn (deriv f) (Set.Icc a b)) : ContDiffOn ℝ 1 f (Set.Icc a b) := by
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Icc hab)]
  refine ⟨fun x hx => (hf x hx).differentiableWithinAt, hc.congr ?_⟩
  intro x hx
  exact (hf x hx).derivWithin ((uniqueDiffOn_Icc hab) x hx)

/-- The differentiated amplitude is the actual derivative of g(x) exp(2πif(x)). -/
theorem weighted_wave_hasDerivAt {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    HasDerivAt (fun u => (g u : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (f u : ℂ)))
      ((((deriv g x : ℝ) : ℂ) + 2 * Real.pi * Complex.I * (g x : ℂ) * ((deriv f x : ℝ) : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (f x : ℂ))) x := by
  have he := ((hf.hasDerivAt.ofReal_comp).const_mul (2 * Real.pi * Complex.I)).cexp
  convert hg.hasDerivAt.ofReal_comp.mul he using 1
  ring

/-- Splitting the actual two-term derivative amplitude costs only the triangle inequality. -/
theorem norm_integral_two_amplitudes_le {a b : ℝ} (h k z : ℝ → ℂ) (c : ℂ)
    (hh : IntervalIntegrable (fun x => h x * z x) volume a b)
    (hk : IntervalIntegrable (fun x => k x * z x) volume a b) :
    ‖∫ x in a..b, (h x + c * k x) * z x‖ ≤
      ‖∫ x in a..b, h x * z x‖ + ‖c‖ * ‖∫ x in a..b, k x * z x‖ := by
  simp_rw [add_mul, mul_assoc]
  rw [intervalIntegral.integral_add hh (hk.const_mul c), intervalIntegral.integral_const_mul]
  simpa only [norm_mul] using norm_add_le (∫ x in a..b, h x * z x) (c * ∫ x in a..b, k x * z x)

/-- Continuous real amplitudes and phases give the genuine complex integrability input. -/
theorem intervalIntegrable_amplitude_phase {a b : ℝ} (hab : a ≤ b) {h φ : ℝ → ℝ}
    (hh : ContinuousOn h (Set.Icc a b)) (hφ : ContinuousOn φ (Set.Icc a b)) :
    IntervalIntegrable (fun x => (h x : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (φ x : ℂ))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  exact (Complex.continuous_ofReal.comp_continuousOn hh).mul
    ((continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφ)).cexp)

/-- The complete differentiated amplitude in the upper-frequency tail, with the source constant. -/
theorem negative_derivative_amplitude_integral_bound {a b ν : ℝ} (hab : a < b) (f g : ℝ → ℝ)
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hfp : ∀ x ∈ Set.Icc a b, 0 ≤ deriv f x)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hgc : ContinuousOn g (Set.Icc a b)) (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ x ∈ Set.Icc a b, 0 ≤ g x) (hga : AntitoneOn g (Set.Icc a b))
    (hgda : AntitoneOn (fun x => |deriv g x|) (Set.Icc a b)) (hν : deriv f a < ν) :
    ‖∫ x in a..b, (((deriv g x : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((g x * deriv f x : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((f x - ν * x : ℝ) : ℂ))‖ ≤
        (|deriv g a| + 2 * Real.pi * g a * deriv f a) / (Real.pi * (ν - deriv f a)) := by
  have hf := contDiffOn_one_of_continuous_deriv hab hfd hfc
  have hphase : ContinuousOn (fun x => f x - ν * x) (Set.Icc a b) :=
    hf.continuousOn.sub (continuousOn_const.mul continuousOn_id)
  have hi := norm_integral_two_amplitudes_le (fun x => ((deriv g x : ℝ) : ℂ))
    (fun x => ((g x * deriv f x : ℝ) : ℂ))
    (fun x => Complex.exp (2 * Real.pi * Complex.I * ((f x - ν * x : ℝ) : ℂ)))
    (2 * Real.pi * Complex.I)
    (intervalIntegrable_amplitude_phase hab.le hgdc hphase)
    (intervalIntegrable_amplitude_phase hab.le (hgc.mul hfc) hphase)
  have h1 := negative_frequency_integral_bound hab f (deriv g) hf hfd hfc hfa hgdc hgda hν
  have h2 := negative_frequency_integral_bound hab f (fun x => g x * deriv f x) hf hfd hfc hfa
    (hgc.mul hfc) (weighted_slope_abs_antitone hgp hfp hga hfa) hν
  have hnorm : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp
  rw [hnorm] at hi
  have ha : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  rw [abs_of_nonneg (mul_nonneg (hgp a ha) (hfp a ha))] at h2
  have hb := hi.trans (add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by positivity)))
  convert hb using 1
  ring

/-- The complete differentiated amplitude in the lower-frequency tail uses the accepted repair. -/
theorem positive_derivative_amplitude_integral_bound {a b ν : ℝ} (hab : a < b) (f g : ℝ → ℝ)
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b))
    (hfp : ∀ x ∈ Set.Icc a b, 0 ≤ deriv f x)
    (hfa : AntitoneOn (deriv f) (Set.Icc a b))
    (hgc : ContinuousOn g (Set.Icc a b)) (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ x ∈ Set.Icc a b, 0 ≤ g x) (hga : AntitoneOn g (Set.Icc a b))
    (hgdq : AntitoneOn (fun x => |deriv g x| / (1 + deriv f x)) (Set.Icc a b)) (hν : 1 ≤ ν) :
    ‖∫ x in a..b, (((deriv g x : ℝ) : ℂ) + 2 * Real.pi * Complex.I * ((g x * deriv f x : ℝ) : ℂ)) *
      Complex.exp (2 * Real.pi * Complex.I * ((f x + ν * x : ℝ) : ℂ))‖ ≤
        (|deriv g a| + 2 * Real.pi * g a * deriv f a) / (Real.pi * (ν + deriv f a)) := by
  have hf := contDiffOn_one_of_continuous_deriv hab hfd hfc
  have hphase : ContinuousOn (fun x => f x + ν * x) (Set.Icc a b) :=
    hf.continuousOn.add (continuousOn_const.mul continuousOn_id)
  have hi := norm_integral_two_amplitudes_le (fun x => ((deriv g x : ℝ) : ℂ))
    (fun x => ((g x * deriv f x : ℝ) : ℂ))
    (fun x => Complex.exp (2 * Real.pi * Complex.I * ((f x + ν * x : ℝ) : ℂ)))
    (2 * Real.pi * Complex.I)
    (intervalIntegrable_amplitude_phase hab.le hgdc hphase)
    (intervalIntegrable_amplitude_phase hab.le (hgc.mul hfc) hphase)
  have h1 := positive_frequency_integral_bound hab f (deriv g) hf hfd hfc hfp hfa hgdc hgdq hν
  have h2 := positive_frequency_integral_bound hab f (fun x => g x * deriv f x) hf hfd hfc hfp hfa
    (hgc.mul hfc) (weighted_slope_quotient_antitone hgp hfp hga hfa) hν
  have hnorm : ‖(2 * Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
    simp
  rw [hnorm] at hi
  have ha : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  rw [abs_of_nonneg (mul_nonneg (hgp a ha) (hfp a ha))] at h2
  have hb := hi.trans (add_le_add h1 (mul_le_mul_of_nonneg_left h2 (by positivity)))
  convert hb using 1
  ring

end DhimanKadiriQuesadaHerrera2026
