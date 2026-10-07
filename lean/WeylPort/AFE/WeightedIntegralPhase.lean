module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.WeightedIntegrals

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # The logarithmic phase below its first positive stationary point

The absolute-height condition treats positive and negative heights explicitly.
All quotient monotonicity is derived for the actual power amplitude.
-/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory
open scoped Topology

/-- The real phase of u⁻ˢ exp(2πimu). -/
noncomputable def weightedIntegralPhase (t m u : ℝ) : ℝ :=
  2 * Real.pi * m * u - t * Real.log u

/-- Its actual derivative at every positive argument. -/
theorem weightedIntegralPhase_hasDerivAt (t m : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (weightedIntegralPhase t m) (2 * Real.pi * m - t / u) u := by
  unfold weightedIntegralPhase
  simpa only [id_eq, one_mul, mul_one, div_eq_mul_inv] using
    ((hasDerivAt_id u).const_mul (2 * Real.pi * m)).fun_sub ((Real.hasDerivAt_log hu.ne').const_mul t)

/-- The absolute-height cutoff excludes a stationary point on the whole lower interval. -/
theorem weightedIntegralPhase_deriv_ne_zero {t m b u : ℝ} (hm : 0 ≤ m)
    (hu : 0 < u) (hub : u ≤ b) (hcut : 2 * Real.pi * m * b < |t|) :
    2 * Real.pi * m - t / u ≠ 0 := by
  intro h
  have he : t = (2 * Real.pi * m) * u := (div_eq_iff hu.ne').mp (by linarith)
  have hA : 0 ≤ 2 * Real.pi * m := by positivity
  rw [he, abs_of_nonneg (mul_nonneg hA hu.le)] at hcut
  nlinarith

/-- The absolute phase derivative decreases for either height sign below the cutoff. -/
theorem abs_weightedIntegralPhase_deriv_antitone {t m a b : ℝ}
    (hm : 0 ≤ m) (ha : 0 < a) (hcut : 2 * Real.pi * m * b < |t|) :
    AntitoneOn (fun u => |2 * Real.pi * m - t / u|) (Set.Icc a b) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := ha.trans_le hx.1
  have hypos : 0 < y := ha.trans_le hy.1
  have hA : 0 ≤ 2 * Real.pi * m := by positivity
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht] at hcut
    have hneg (u : ℝ) (hu : 0 < u) (hub : u ≤ b) : 2 * Real.pi * m - t / u < 0 := by
      have hAu : (2 * Real.pi * m) * u < t := (mul_le_mul_of_nonneg_left hub hA).trans_lt hcut
      have hq := (lt_div_iff₀ hu).mpr hAu
      linarith
    dsimp only
    rw [abs_of_neg (hneg x hxpos hx.2), abs_of_neg (hneg y hypos hy.2)]
    have hq := div_le_div_of_nonneg_left ht hxpos hxy
    linarith
  · have hpos (u : ℝ) (hu : 0 < u) : 0 ≤ 2 * Real.pi * m - t / u :=
      sub_nonneg.mpr ((div_nonpos_of_nonpos_of_nonneg ht hu.le).trans hA)
    dsimp only
    rw [abs_of_nonneg (hpos x hxpos), abs_of_nonneg (hpos y hypos)]
    have hq := div_le_div_of_nonneg_left (neg_nonneg.mpr ht) hxpos hxy
    simp only [neg_div] at hq
    linarith

/-- The actual nonnegative power amplitude satisfies the increasing quotient condition. -/
theorem weightedIntegralPhase_quotient_monotone {r t m a b : ℝ}
    (hr : 0 ≤ r) (hm : 0 ≤ m) (ha : 0 < a) (hcut : 2 * Real.pi * m * b < |t|) :
    MonotoneOn (fun u => |u ^ r / (2 * Real.pi * m - t / u)|) (Set.Icc a b) := by
  intro x hx y hy hxy
  have hxpos : 0 < x := ha.trans_le hx.1
  have hypos : 0 < y := ha.trans_le hy.1
  dsimp only
  rw [abs_div, abs_div, abs_of_pos (Real.rpow_pos_of_pos hxpos r),
    abs_of_pos (Real.rpow_pos_of_pos hypos r)]
  calc
    _ ≤ y ^ r / |2 * Real.pi * m - t / x| :=
      div_le_div_of_nonneg_right (Real.rpow_le_rpow hxpos.le hxy hr) (abs_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left (Real.rpow_nonneg hypos.le r)
      (abs_pos.mpr (weightedIntegralPhase_deriv_ne_zero hm hypos hy.2 hcut))
      (abs_weightedIntegralPhase_deriv_antitone hm ha hcut hx hy hxy)

/-- The exact first-derivative bound for the source phase on every truncated lower interval. -/
theorem norm_integral_power_log_phase_le {r t m a b : ℝ}
    (hr : 0 ≤ r) (hm : 0 ≤ m) (ha : 0 < a) (hab : a < b)
    (hcut : 2 * Real.pi * m * b < |t|) :
    ‖∫ u in a..b, ((u ^ r : ℝ) : ℂ) *
      Complex.exp (Complex.I * (weightedIntegralPhase t m u : ℂ))‖ ≤
      2 * b ^ r / |2 * Real.pi * m - t / b| := by
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  have hc : ContinuousOn (fun u => 2 * Real.pi * m - t / u) (Set.Icc a b) :=
    continuousOn_const.sub (continuousOn_const.div continuousOn_id (fun u hu => (hp u hu).ne'))
  have h := first_derivative_test_monotone hab
    (fun u hu => weightedIntegralPhase_hasDerivAt t m (hp u hu)) hc
    (Real.continuous_rpow_const hr).continuousOn
    (fun u hu => weightedIntegralPhase_deriv_ne_zero hm (hp u hu) hu.2 hcut)
    (weightedIntegralPhase_quotient_monotone hr hm ha hcut)
  rw [abs_div, abs_of_pos (Real.rpow_pos_of_pos (ha.trans hab) r)] at h
  simpa only [mul_div_assoc] using h

/-- The physical distance from the cutoff gives the source's uniform endpoint bound. -/
theorem norm_integral_power_log_phase_distance_le {r t m a b : ℝ}
    (hr : 0 ≤ r) (hm : 0 ≤ m) (ha : 0 < a) (hab : a < b)
    (hcut : 2 * Real.pi * m * b < |t|) :
    ‖∫ u in a..b, ((u ^ r : ℝ) : ℂ) *
      Complex.exp (Complex.I * (weightedIntegralPhase t m u : ℂ))‖ ≤
      2 * b ^ (r + 1) / (|t| - 2 * Real.pi * m * b) := by
  have hb : 0 < b := ha.trans hab
  have hd : 0 < |t| - 2 * Real.pi * m * b := by linarith
  have he : |2 * Real.pi * m - t / b| = |t - 2 * Real.pi * m * b| / b := by
    rw [show 2 * Real.pi * m - t / b = -(t - 2 * Real.pi * m * b) / b by field_simp; ring,
      abs_div, abs_neg, abs_of_pos hb]
  have hl : (|t| - 2 * Real.pi * m * b) / b ≤ |2 * Real.pi * m - t / b| := by
    rw [he]
    apply div_le_div_of_nonneg_right _ hb.le
    simpa only [abs_of_nonneg (show 0 ≤ 2 * Real.pi * m * b by positivity)] using
      (abs_sub_abs_le_abs_sub t (2 * Real.pi * m * b))
  calc
    _ ≤ 2 * b ^ r / |2 * Real.pi * m - t / b| :=
      norm_integral_power_log_phase_le hr hm ha hab hcut
    _ ≤ 2 * b ^ r / ((|t| - 2 * Real.pi * m * b) / b) :=
      div_le_div_of_nonneg_left (by positivity) (div_pos hd hb) hl
    _ = _ := by rw [div_div_eq_mul_div, Real.rpow_add_one hb.ne']; ring

/-- The phase/amplitude representation agrees with the actual principal complex-power integrand. -/
theorem cpow_linear_wave_eq_power_log_phase (r t m : ℝ) {u : ℝ} (hu : 0 < u) :
    (u : ℂ) ^ ((r : ℂ) - (t : ℂ) * Complex.I) *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * (u : ℂ)) =
    ((u ^ r : ℝ) : ℂ) * Complex.exp (Complex.I * (weightedIntegralPhase t m u : ℂ)) := by
  rw [Real.rpow_def_of_pos hu, Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'),
    ← Complex.ofReal_log hu.le, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  unfold weightedIntegralPhase
  push_cast
  ring

/-- The actual remainder integral after two integrations by parts has the source endpoint estimate. -/
theorem norm_weightedIntegral_shift_two_le {σ t m a b : ℝ}
    (hσ : σ ≤ 2) (hm : 0 ≤ m) (ha : 0 < a) (hab : a < b)
    (hcut : 2 * Real.pi * m * b < |t|) :
    ‖weightedIntegral (((σ : ℂ) + (t : ℂ) * Complex.I) - 2) a b m‖ ≤
      2 * b ^ (3 - σ) / (|t| - 2 * Real.pi * m * b) := by
  have he : weightedIntegral (((σ : ℂ) + (t : ℂ) * Complex.I) - 2) a b m =
      ∫ u in a..b, ((u ^ (2 - σ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (weightedIntegralPhase t m u : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hup : 0 < u := ha.trans_le ((Set.uIcc_of_le hab.le ▸ hu).1)
    rw [show -(((σ : ℂ) + (t : ℂ) * Complex.I) - 2) =
      (((2 - σ : ℝ) : ℂ) - (t : ℂ) * Complex.I) by push_cast; ring]
    exact cpow_linear_wave_eq_power_log_phase (2 - σ) t m hup
  rw [he]
  simpa only [show 2 - σ + 1 = 3 - σ by ring] using
    norm_integral_power_log_phase_distance_le (by linarith : 0 ≤ 2 - σ) hm ha hab hcut

/-- The actual finite J integral depends continuously on its lower endpoint. -/
theorem continuous_weightedIntegral_left {s : ℂ} (hs : s.re < 1) (b m : ℝ) :
    Continuous (fun a => weightedIntegral s a b m) := by
  have h := (intervalIntegral.continuous_primitive
    (fun a b => intervalIntegrable_weighted_integrand hs a b m) b).neg
  simpa only [weightedIntegral, Pi.neg_def, ← intervalIntegral.integral_symm] using h

/-- Passing to the integrable zero endpoint proves the full lower-interval remainder bound. -/
theorem norm_weightedIntegral_shift_two_zero_le {σ t m b : ℝ}
    (hσ : σ ≤ 2) (hm : 0 ≤ m) (hb : 0 < b) (hcut : 2 * Real.pi * m * b < |t|) :
    ‖weightedIntegral (((σ : ℂ) + (t : ℂ) * Complex.I) - 2) 0 b m‖ ≤
      2 * b ^ (3 - σ) / (|t| - 2 * Real.pi * m * b) := by
  have hs : (((σ : ℂ) + (t : ℂ) * Complex.I) - 2).re < 1 := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
    linarith
  have ht := ((continuous_weightedIntegral_left hs b m).tendsto 0).norm.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT hb] with a ha
  exact norm_weightedIntegral_shift_two_le hσ hm ha.1 ha.2 hcut

/-- Linking the cutoff to the physical height gives the exact Lemma-5 remainder factor. -/
theorem norm_weightedIntegral_shift_two_source {σ t m x y : ℝ}
    (hσ : σ ≤ 2) (hm : 0 ≤ m) (hx : 0 < x) (hmy : m < y)
    (hscale : 2 * Real.pi * x * y = |t|) :
    ‖weightedIntegral (((σ : ℂ) + (t : ℂ) * Complex.I) - 2) 0 x m‖ ≤
      x ^ (2 - σ) / (Real.pi * (y - m)) := by
  have hcut : 2 * Real.pi * m * x < |t| := by
    rw [← hscale]
    nlinarith [mul_pos Real.two_pi_pos hx]
  have h := norm_weightedIntegral_shift_two_zero_le hσ hm hx hcut
  rw [← hscale] at h
  have he : 2 * x ^ (3 - σ) / (2 * Real.pi * x * y - 2 * Real.pi * m * x) =
      x ^ (2 - σ) / (Real.pi * (y - m)) := by
    rw [show 3 - σ = (2 - σ) + 1 by ring, Real.rpow_add_one hx.ne']
    field_simp
  rwa [he] at h

end DhimanKadiriQuesadaHerrera2026
