module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.FiniteExponentialSums
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Group.Tannery

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A bounded Abel approximation to the actual sawtooth

The unit-interval phase factorization and argument calculation adapt the
Apache-2.0 proofs in the existing node-71
`GuthMaynardExternal/PNT/ZetaAppendix.lean` (SHA-256
9fad94d5a7026d86882df61147b1082b103caf555ac803f0b1b52efd8bc28d9f).
The logarithmic Abel kernel supplies a uniform bound before integration.
-/

namespace DhimanKadiriQuesadaHerrera2026

open scoped Topology
open Filter MeasureTheory

/-- The actual positive unit-frequency Fourier exponential. -/
noncomputable def positivePhase (x : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- A logarithmic Abel kernel for fract(x)-1/2 away from the integers. -/
noncomputable def abelSawtooth (r x : ℝ) : ℝ :=
  (Complex.log (1 - (r : ℂ) * positivePhase x)).im / Real.pi

/-- The positive Fourier phase has unit norm. -/
theorem norm_positivePhase (x : ℝ) : ‖positivePhase x‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- The two sign conventions refer to the same actual exponential. -/
theorem positivePhase_eq_expMode (x : ℝ) : positivePhase x = expMode (-x) 1 := by
  unfold positivePhase expMode
  congr 1
  push_cast
  ring

/-- No noninteger point is a unit-phase singularity. -/
theorem positivePhase_ne_one {x : ℝ} (hx : ∀ k : ℤ, x ≠ (k : ℝ)) : positivePhase x ≠ 1 := by
  rw [positivePhase_eq_expMode]
  apply expMode_one_ne_one
  apply sin_pi_mul_ne_zero_of_noninteger
  intro k hk
  apply hx (-k)
  push_cast
  linarith

/-- Integral translation leaves the actual Fourier phase unchanged. -/
theorem positivePhase_add_int (x : ℝ) (k : ℤ) : positivePhase (x + k) = positivePhase x := by
  unfold positivePhase
  rw [show (((2 * Real.pi * (x + k) : ℝ) : ℂ) * Complex.I) =
    (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) + (k : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The phase reduces to the fractional part for every real argument. -/
theorem positivePhase_fract (x : ℝ) : positivePhase x = positivePhase (Int.fract x) := by
  simpa only [Int.fract_add_floor] using positivePhase_add_int (Int.fract x) ⌊x⌋

/-- At radius one, the logarithm avoids its branch cut away from the integers. -/
theorem one_sub_positivePhase_mem_slitPlane {x : ℝ} (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    1 - positivePhase x ∈ Complex.slitPlane := by
  have hne : 1 - positivePhase x ≠ 0 := sub_ne_zero.mpr (positivePhase_ne_one hx).symm
  have hre : 0 ≤ (1 - positivePhase x).re := by
    simp only [positivePhase, Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re]
    exact sub_nonneg.mpr (Real.cos_le_one _)
  rw [Complex.mem_slitPlane_iff]
  by_cases him : (1 - positivePhase x).im = 0
  · exact Or.inl (lt_of_le_of_ne' hre (fun h => hne (Complex.ext h him)))
  · exact Or.inr him

/-- The exact phase factorization fixes the logarithm branch on the unit interval. -/
theorem one_sub_positivePhase_factor (x : ℝ) :
    1 - positivePhase x = (2 * Real.sin (Real.pi * x) : ℝ) *
      Complex.exp (((Real.pi * x - Real.pi / 2 : ℝ) : ℂ) * Complex.I) := by
  apply Complex.ext
  · simp only [positivePhase, Complex.sub_re, Complex.one_re, Complex.exp_ofReal_mul_I_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
    simp [Real.cos_sub, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi * x)]
  · simp only [positivePhase, Complex.sub_im, Complex.one_im, Complex.exp_ofReal_mul_I_im,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [show 2 * Real.pi * x = 2 * (Real.pi * x) by ring]
    simp [Real.sin_sub, Real.sin_two_mul]

/-- The source sawtooth sign follows from the principal argument, not a formal series swap. -/
theorem arg_one_sub_positivePhase {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Complex.arg (1 - positivePhase x) = Real.pi * x - Real.pi / 2 := by
  have hs : 0 < Real.sin (Real.pi * x) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx) (by nlinarith [Real.pi_pos])
  have hθ : Real.pi * x - Real.pi / 2 ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor <;> nlinarith [Real.pi_pos]
  rw [one_sub_positivePhase_factor, Complex.arg_real_mul _ (by positivity)]
  exact (Complex.arg_exp_mul_I _).trans
    ((toIocMod_eq_self Real.two_pi_pos).mpr (by simpa [two_mul] using hθ))

/-- The limiting kernel is precisely the positive sawtooth at every noninteger point. -/
theorem abelSawtooth_one {x : ℝ} (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    abelSawtooth 1 x = Int.fract x - 1 / 2 := by
  have hfract : 0 < Int.fract x := by
    have hn : Int.fract x ≠ 0 := by
      intro h
      obtain ⟨k, hk⟩ := Int.fract_eq_zero_iff.mp h
      exact hx k hk.symm
    exact lt_of_le_of_ne (Int.fract_nonneg x) hn.symm
  unfold abelSawtooth
  simp only [Complex.ofReal_one, one_mul, Complex.log_im]
  rw [positivePhase_fract, arg_one_sub_positivePhase hfract (Int.fract_lt_one x)]
  field_simp

/-- The logarithmic kernel is uniformly bounded, including near every integer. -/
theorem abs_abelSawtooth_le (r x : ℝ) : |abelSawtooth r x| ≤ 1 := by
  unfold abelSawtooth
  rw [abs_div, Complex.log_im, abs_of_pos Real.pi_pos]
  exact (div_le_one Real.pi_pos).mpr (Complex.abs_arg_le_pi _)

/-- Radial Abel limits converge to the actual sawtooth away from integers. -/
theorem tendsto_abelSawtooth {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 1))
    {x : ℝ} (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    Tendsto (fun n => abelSawtooth (r n) x) atTop (𝓝 (Int.fract x - 1 / 2)) := by
  have ht : Tendsto (fun n => (1 : ℂ) - (r n : ℂ) * positivePhase x) atTop
      (𝓝 (1 - positivePhase x)) := by
    simpa using tendsto_const_nhds.sub (hr.ofReal.mul_const (positivePhase x))
  have hl := ((Complex.continuous_im.tendsto _).comp
    (ht.clog (one_sub_positivePhase_mem_slitPlane hx))).div_const Real.pi
  rw [← abelSawtooth_one hx]
  simpa only [abelSawtooth, Complex.ofReal_one, one_mul, Function.comp_def] using hl

/-- The actual phase is continuous on the whole real line. -/
theorem continuous_positivePhase : Continuous positivePhase := by
  unfold positivePhase
  fun_prop

/-- Inside the unit disk, every logarithm argument lies in the open right half-plane. -/
theorem radial_phase_mem_slitPlane {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    1 - (r : ℂ) * positivePhase x ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hre : (positivePhase x).re ≤ 1 := by
    simpa only [norm_positivePhase] using Complex.re_le_norm (positivePhase x)
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hre)]

/-- Every damped kernel is continuous, including at integer points. -/
theorem continuous_abelSawtooth {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (abelSawtooth r) := by
  unfold abelSawtooth
  exact (Complex.continuous_im.comp
    ((continuous_const.sub (continuous_const.mul continuous_positivePhase)).clog
      (radial_phase_mem_slitPlane hr0 hr1))).div_const Real.pi

/-- The damped logarithm has its actual absolutely convergent Fourier expansion. -/
theorem hasSum_abelSawtooth {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasSum (fun n : ℕ => -(((r : ℂ) * positivePhase x) ^ n / (n : ℂ)).im / Real.pi)
      (abelSawtooth r x) := by
  have hz : ‖(r : ℂ) * positivePhase x‖ < 1 := by
    rw [norm_mul, norm_positivePhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    exact hr1
  have h := (Complex.hasSum_im (Complex.hasSum_taylorSeries_neg_log hz)).neg.div_const Real.pi
  simpa only [Complex.neg_im, neg_neg, abelSawtooth] using h

/-- Integer points form a null set for every atomless measure on the real line. -/
theorem ae_noninteger (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ x ∂μ, ∀ k : ℤ, x ≠ (k : ℝ) :=
  ae_all_iff.mpr (fun k => μ.ae_ne (k : ℝ))

/-- The uniformly bounded Abel kernels may be passed through the actual weighted integral. -/
theorem tendsto_integral_mul_abelSawtooth {μ : Measure ℝ} [NullSingletonClass μ]
    {h : ℝ → ℂ} (hh : Integrable h μ) {r : ℕ → ℝ}
    (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n < 1) (hr : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, h x * (abelSawtooth (r n) x : ℂ) ∂μ) atTop
      (𝓝 (∫ x, h x * ((Int.fract x - 1 / 2 : ℝ) : ℂ) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖h x‖)
  · intro n
    exact hh.aestronglyMeasurable.mul
      (Complex.continuous_ofReal.comp (continuous_abelSawtooth (hr0 n) (hr1 n))).aestronglyMeasurable
  · exact hh.norm
  · intro n
    filter_upwards with x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (norm_nonneg _) (abs_abelSawtooth_le _ _)
  · filter_upwards [ae_noninteger μ] with x hx
    exact (tendsto_abelSawtooth hr hx).ofReal.const_mul (h x)


/-- The paired positive and negative Fourier modes of the positive sawtooth. -/
noncomputable def sawtoothMode (n : ℕ) (x : ℝ) : ℂ :=
  (expMode x n - expMode (-x) n) / (2 * Real.pi * Complex.I * n)

/-- Complex conjugation changes the Fourier sign. -/
theorem conj_expMode (x : ℝ) (n : ℕ) :
    starRingEnd ℂ (expMode x n) = expMode (-x) n := by
  unfold expMode
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The logarithmic expansion term is exactly the paired Fourier coefficient. -/
theorem abelSawtooth_term_eq (r x : ℝ) (n : ℕ) :
    ((-(((r : ℂ) * positivePhase x) ^ n / (n : ℂ)).im / Real.pi : ℝ) : ℂ) =
      (r : ℂ) ^ n * sawtoothMode n x := by
  rw [Complex.ofReal_div, Complex.ofReal_neg, Complex.im_eq_sub_conj]
  simp only [map_div₀, map_pow, map_mul, Complex.conj_ofReal, map_natCast,
    positivePhase_eq_expMode, conj_expMode, neg_neg, mul_pow]
  rw [← expMode_eq_pow, ← expMode_eq_pow]
  unfold sawtoothMode
  ring

/-- The paired Fourier series of each damped kernel converges absolutely. -/
theorem hasSum_abelSawtooth_modes {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasSum (fun n : ℕ => (r : ℂ) ^ n * sawtoothMode n x) (abelSawtooth r x : ℂ) := by
  simpa only [abelSawtooth_term_eq] using Complex.hasSum_ofReal.mpr (hasSum_abelSawtooth hr0 hr1 x)

/-- The paired coefficient is continuous, including its zero-frequency value. -/
theorem continuous_sawtoothMode (n : ℕ) : Continuous (sawtoothMode n) := by
  unfold sawtoothMode expMode
  fun_prop

/-- A geometric-series majorant for the paired Fourier coefficients. -/
theorem norm_sawtoothMode_le (n : ℕ) (x : ℝ) : ‖sawtoothMode n x‖ ≤ 1 / Real.pi := by
  by_cases hn : n = 0
  · simp [sawtoothMode, hn]
    positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hden : 0 < 2 * Real.pi * n := by positivity
  rw [sawtoothMode, norm_div, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I, mul_one, Complex.norm_natCast]
  apply (div_le_iff₀ hden).mpr
  have ht := norm_sub_le (expMode x n) (expMode (-x) n)
  rw [norm_expMode, norm_expMode] at ht
  calc
    ‖expMode x n - expMode (-x) n‖ ≤ 2 := by norm_num at ht ⊢; exact ht
    _ ≤ (1 / Real.pi) * (2 * Real.pi * n) := by
      field_simp
      linarith


/-- Multiplying an integrable amplitude by a Fourier coefficient preserves integrability. -/
theorem integrable_mul_sawtoothMode {μ : Measure ℝ} {h : ℝ → ℂ}
    (hh : Integrable h μ) (n : ℕ) : Integrable (fun x => h x * sawtoothMode n x) μ :=
  hh.mul_bdd (continuous_sawtoothMode n).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_sawtoothMode_le n))

/-- Absolute geometric domination justifies the damped Fourier series under the integral. -/
theorem hasSum_integral_abelSawtooth {μ : Measure ℝ} {h : ℝ → ℂ}
    (hh : Integrable h μ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun n : ℕ => (r : ℂ) ^ n * ∫ x, h x * sawtoothMode n x ∂μ)
      (∫ x, h x * (abelSawtooth r x : ℂ) ∂μ) := by
  let F : ℕ → ℝ → ℂ := fun n x => (r : ℂ) ^ n * (h x * sawtoothMode n x)
  have hFi (n : ℕ) : Integrable (F n) μ :=
    (integrable_mul_sawtoothMode hh n).const_mul _
  have hbound (n : ℕ) (x : ℝ) : ‖F n x‖ ≤ r ^ n * (‖h x‖ / Real.pi) := by
    dsimp only [F]
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      norm_mul]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0 n)
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_left (norm_sawtoothMode_le n x) (norm_nonneg (h x))
  have hsum : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    apply ((summable_geometric_of_lt_one hr0 hr1).mul_right
      ((∫ x, ‖h x‖ ∂μ) / Real.pi)).of_nonneg_of_le
      (fun n => integral_nonneg (fun x => norm_nonneg (F n x)))
    intro n
    calc
      (∫ x, ‖F n x‖ ∂μ) ≤ ∫ x, r ^ n * (‖h x‖ / Real.pi) ∂μ :=
        integral_mono (hFi n).norm ((hh.norm.div_const _).const_mul _) (hbound n)
      _ = r ^ n * ((∫ x, ‖h x‖ ∂μ) / Real.pi) := by
        rw [integral_const_mul, integral_div]
  have hpoint (x : ℝ) : (∑' n, F n x) = h x * (abelSawtooth r x : ℂ) := by
    have hs := (hasSum_abelSawtooth_modes hr0 hr1 x).mul_left (h x)
    convert hs.tsum_eq using 1
    congr 1
    funext n
    dsimp only [F]
    ring
  have hi := hasSum_integral_of_summable_integral_norm hFi hsum
  simp_rw [hpoint] at hi
  simpa only [F, integral_const_mul] using hi


/-- Abel damping tends to the sum of an absolutely convergent complex series. -/
theorem tendsto_tsum_abel {c : ℕ → ℂ} (hc : Summable c) {r : ℕ → ℝ}
    (hr0 : ∀ n, 0 ≤ r n) (hr1 : ∀ n, r n ≤ 1) (hr : Tendsto r atTop (𝓝 1)) :
    Tendsto (fun k => ∑' n, (r k : ℂ) ^ n * c n) atTop (𝓝 (∑' n, c n)) := by
  apply tendsto_tsum_of_dominated_convergence hc.norm
  · intro n
    simpa only [Complex.ofReal_one, one_pow, one_mul] using (hr.ofReal.pow n).mul_const (c n)
  · filter_upwards with k n
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hr0 k)]
    exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (hr0 k) (hr1 k))

/-- The actual sawtooth integral equals its paired Fourier integral series whenever the
integrated coefficients are absolutely summable; this condition is discharged by the
nonstationary bounds in the Poisson application. -/
theorem integral_mul_sawtooth_eq_tsum {μ : Measure ℝ} [NullSingletonClass μ] {h : ℝ → ℂ}
    (hh : Integrable h μ) (hs : Summable (fun n : ℕ => ∫ x, h x * sawtoothMode n x ∂μ)) :
    (∫ x, h x * ((Int.fract x - 1 / 2 : ℝ) : ℂ) ∂μ) =
      ∑' n : ℕ, ∫ x, h x * sawtoothMode n x ∂μ := by
  let r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 1)
  have hr0 (n : ℕ) : 0 ≤ r n := by
    dsimp only [r]
    exact sub_nonneg.mpr ((div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  have hr1 (n : ℕ) : r n < 1 := by
    dsimp only [r]
    have : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hr : Tendsto r atTop (𝓝 1) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  have hi := tendsto_integral_mul_abelSawtooth hh hr0 hr1 hr
  have ht := tendsto_tsum_abel hs hr0 (fun n => (hr1 n).le) hr
  have he (n : ℕ) := (hasSum_integral_abelSawtooth hh (hr0 n) (hr1 n)).tsum_eq
  simp_rw [he] at ht
  exact tendsto_nhds_unique hi ht

end DhimanKadiriQuesadaHerrera2026
