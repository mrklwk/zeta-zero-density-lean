module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.WeightedIntegralPhase
public import WeylPort.AFE.MonotoneAmplitude
public import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Bounds above the stationary region for the actual weighted integrals

The unit-amplitude first-derivative bound is transferred to the decreasing
power amplitude by integration by parts. This works for both height signs
without asserting the printed quotient monotonicity for negative heights.
-/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory
open scoped Topology

/-- Above the signed cutoff, the actual phase derivative has a uniform positive lower bound. -/
theorem upper_phase_derivative_lower {t m a u : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hau : a ≤ u) (hcut : t < Real.pi * m * a) :
    Real.pi * m < 2 * Real.pi * m - t / u := by
  have hu : 0 < u := ha.trans_le hau
  have hmul : t < (Real.pi * m) * u :=
    hcut.trans_le (mul_le_mul_of_nonneg_left hau (by positivity))
  have hdiv := (div_lt_iff₀ hu).mpr hmul
  linarith

/-- The reciprocal of the positive derivative is monotone, in one direction for each sign. -/
theorem upper_phase_reciprocal_monotone {t m a b : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hcut : t < Real.pi * m * a) :
    MonotoneOn (fun u => |1 / (2 * Real.pi * m - t / u)|) (Set.Icc a b) ∨
      AntitoneOn (fun u => |1 / (2 * Real.pi * m - t / u)|) (Set.Icc a b) := by
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < 2 * Real.pi * m - t / u :=
    lt_trans (by positivity) (upper_phase_derivative_lower hm ha hu.1 hcut)
  rcases le_total 0 t with ht | ht
  · right
    intro x hx y hy hxy
    dsimp only
    rw [abs_of_pos (one_div_pos.mpr (hd x hx)), abs_of_pos (one_div_pos.mpr (hd y hy))]
    apply one_div_le_one_div_of_le (hd x hx)
    have h := div_le_div_of_nonneg_left ht (ha.trans_le hx.1) hxy
    linarith
  · left
    intro x hx y hy hxy
    dsimp only
    rw [abs_of_pos (one_div_pos.mpr (hd x hx)), abs_of_pos (one_div_pos.mpr (hd y hy))]
    apply one_div_le_one_div_of_le (hd y hy)
    have h := div_le_div_of_nonneg_left (neg_nonneg.mpr ht) (ha.trans_le hx.1) hxy
    simp only [neg_div] at h
    linarith

/-- The actual unweighted oscillatory primitive is uniformly bounded above the signed cutoff. -/
theorem norm_integral_upper_phase_le {t m a b : ℝ} (hm : 0 < m) (ha : 0 < a)
    (hab : a ≤ b) (hcut : t < Real.pi * m * a) :
    ‖∫ u in a..b, Complex.exp (Complex.I * (weightedIntegralPhase t m u : ℂ))‖ ≤
      2 / (Real.pi * m) := by
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < 2 * Real.pi * m - t / u :=
    lt_trans (by positivity) (upper_phase_derivative_lower hm ha hu.1 hcut)
  have h := first_derivative_test hab
    (fun u hu => weightedIntegralPhase_hasDerivAt t m (hp u hu))
    (continuousOn_const.sub (continuousOn_const.div continuousOn_id (fun u hu => (hp u hu).ne')))
    (g := fun _ => 1) continuousOn_const (fun u hu => (hd u hu).ne')
    (upper_phase_reciprocal_monotone hm ha hcut)
  simp only [Complex.ofReal_one, one_mul] at h
  have he (u : ℝ) (hu : u ∈ Set.Icc a b) :
      |1 / (2 * Real.pi * m - t / u)| ≤ 1 / (Real.pi * m) := by
    rw [abs_of_pos (one_div_pos.mpr (hd u hu))]
    exact one_div_le_one_div_of_le (by positivity)
      (upper_phase_derivative_lower hm ha hu.1 hcut).le
  exact h.trans (by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
      (max_le (he a (Set.left_mem_Icc.mpr hab)) (he b (Set.right_mem_Icc.mpr hab)))
        (by norm_num : (0 : ℝ) ≤ 2))


/-- The oscillatory phase factor is continuous on its actual positive domain. -/
theorem continuousOn_upper_phase (t m : ℝ) :
    ContinuousOn (fun u => Complex.exp (Complex.I * (weightedIntegralPhase t m u : ℂ)))
      (Set.Ioi 0) := by
  intro u hu
  exact (Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul
    (Complex.continuous_ofReal.continuousAt.comp
      (weightedIntegralPhase_hasDerivAt t m hu).continuousAt))).continuousWithinAt

/-- The actual oscillatory primitive has the required derivative at each positive point. -/
theorem upper_phase_primitive_hasDerivAt (t m : ℝ) {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    HasDerivAt (fun v => ∫ x in a..v,
      Complex.exp (Complex.I * (weightedIntegralPhase t m x : ℂ)))
        (Complex.exp (Complex.I * (weightedIntegralPhase t m u : ℂ))) u := by
  have hc := continuousOn_upper_phase t m
  have hsub : Set.uIcc a u ⊆ Set.Ioi 0 := by
    intro v hv
    rcases le_total a u with hau | hua
    · exact ha.trans_le ((Set.uIcc_of_le hau ▸ hv).1)
    · exact hu.trans_le ((Set.uIcc_of_ge hua ▸ hv).1)
  exact intervalIntegral.integral_hasDerivAt_right (hc.mono hsub).intervalIntegrable
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hc u hu)
    (hc.continuousAt (isOpen_Ioi.mem_nhds hu))

/-- The full finite upper-tail bound holds for both height signs without extra quotient assumptions. -/
theorem norm_weightedIntegral_upper_le {σ t m a b : ℝ} (hσ : 0 ≤ σ)
    (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b) (hcut : t < Real.pi * m * a) :
    ‖weightedIntegral ((σ : ℂ) + (t : ℂ) * Complex.I) a b m‖ ≤
      2 * a ^ (-σ) / (Real.pi * m) := by
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  have hgc : ContinuousOn (fun u => -σ * u ^ (-σ - 1)) (Set.Icc a b) := by
    intro u hu
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const u (-σ - 1) (Or.inl (hp u hu).ne'))).continuousWithinAt
  have hfc := (continuousOn_upper_phase t m).mono (fun u hu => hp u hu)
  have h := norm_integral_mul_le_of_primitive_bound hab
    (g := fun u => u ^ (-σ)) (g' := fun u => -σ * u ^ (-σ - 1))
    (F := fun v => ∫ x in a..v,
      Complex.exp (Complex.I * (weightedIntegralPhase t m x : ℂ)))
    (fun u hu => Real.hasDerivAt_rpow_const (Or.inl (hp u hu).ne'))
    (fun u hu => upper_phase_primitive_hasDerivAt t m ha (hp u hu)) hgc hfc
    (Real.rpow_nonneg (hp b (Set.right_mem_Icc.mpr hab)).le _)
    (fun u hu => mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ)
      (Real.rpow_nonneg (hp u hu).le _))
    (by simp)
    (fun u hu => norm_integral_upper_phase_le hm ha hu.1 hcut)
  have he : weightedIntegral ((σ : ℂ) + (t : ℂ) * Complex.I) a b m =
      ∫ u in a..b, ((u ^ (-σ) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (weightedIntegralPhase t m u : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hup : 0 < u := hp u (Set.uIcc_of_le hab ▸ hu)
    rw [show -((σ : ℂ) + (t : ℂ) * Complex.I) =
      (((-σ : ℝ) : ℂ) - (t : ℂ) * Complex.I) by push_cast; ring]
    exact cpow_linear_wave_eq_power_log_phase (-σ) t m hup
  rw [he]
  convert h using 1
  ring


/-- Differences of the actual finite integrals are exactly the integral over the intervening tail. -/
theorem weightedIntegral_sub {s : ℂ} (hs : s.re < 1) (a b c m : ℝ) :
    weightedIntegral s a b m - weightedIntegral s a c m = weightedIntegral s c b m :=
  intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_weighted_integrand hs a b m)
    (intervalIntegrable_weighted_integrand hs a c m)

/-- The upper-cutoff family is Cauchy, proving conditional improper convergence from the tail bound. -/
theorem weightedIntegral_cauchy_atTop {σ t m : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hm : 0 < m) (a : ℝ) :
    CauchySeq (fun b : ℝ => weightedIntegral ((σ : ℂ) + (t : ℂ) * Complex.I) a b m) := by
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I).re < 1 := by simpa using hσ.2
  have hlim : Filter.Tendsto (fun R : ℝ => 2 * R ^ (-σ) / (Real.pi * m))
      Filter.atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using (tendsto_rpow_neg_atTop hσ.1).const_mul 2 |>.div_const (Real.pi * m)
  apply Metric.cauchySeq_iff'.mpr
  intro ε hε
  have he := hlim.eventually (gt_mem_nhds hε)
  obtain ⟨R, hR⟩ := (he.and ((Filter.eventually_gt_atTop (0 : ℝ)).and
    (Filter.eventually_gt_atTop (t / (Real.pi * m))))).exists
  refine ⟨R, fun b hb => ?_⟩
  rw [dist_eq_norm, weightedIntegral_sub hs]
  apply (norm_weightedIntegral_upper_le hσ.1.le hm hR.2.1 hb ?_).trans_lt hR.1
  have ht := (div_lt_iff₀ (show 0 < Real.pi * m by positivity)).mp hR.2.2
  nlinarith

/-- J(a,∞,m) denotes the limit of the actual finite interval integrals.
Convergence is established separately; this is not a Bochner integral of a nonintegrable norm. -/
noncomputable def weightedIntegralTail (s : ℂ) (a m : ℝ) : ℂ :=
  Filter.limUnder Filter.atTop (fun b : ℝ => weightedIntegral s a b m)

/-- The actual finite integrals tend to the specified improper integral. -/
theorem weightedIntegral_tendsto_tail {σ t m : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hm : 0 < m) (a : ℝ) :
    Filter.Tendsto (fun b : ℝ => weightedIntegral ((σ : ℂ) + (t : ℂ) * Complex.I) a b m)
      Filter.atTop (𝓝 (weightedIntegralTail ((σ : ℂ) + (t : ℂ) * Complex.I) a m)) :=
  (weightedIntegral_cauchy_atTop hσ hm a).tendsto_limUnder

/-- The single-frequency improper estimate follows by passage to the proved limit. -/
theorem norm_weightedIntegralTail_le {σ t m a : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hm : 0 < m) (ha : 0 < a) (hcut : t < Real.pi * m * a) :
    ‖weightedIntegralTail ((σ : ℂ) + (t : ℂ) * Complex.I) a m‖ ≤
      2 * a ^ (-σ) / (Real.pi * m) := by
  apply le_of_tendsto (weightedIntegral_tendsto_tail hσ hm a).norm
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  exact norm_weightedIntegral_upper_le hσ.1.le hm ha hb hcut


/-- The positive-index harmonic prefix retains the literal real upper cutoff. -/
theorem sum_reciprocals_floor_le {y : ℝ} (hy : 1 ≤ y) :
    (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, 1 / (m : ℝ)) ≤ Real.log y + 1 := by
  have h := harmonic_floor_le_one_add_log y hy
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast,
    one_div, add_comm] using h

/-- The complete second estimate of Lemma 5, with the printed cutoff required for each summed mode. -/
theorem norm_sum_weightedIntegralTail_le {σ t a y : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (ha : 0 < a) (hy : 1 ≤ y)
    (hcut : ∀ m ∈ Finset.Icc 1 ⌊y⌋₊, t < Real.pi * (m : ℝ) * a) :
    ‖∑ m ∈ Finset.Icc 1 ⌊y⌋₊,
      weightedIntegralTail ((σ : ℂ) + (t : ℂ) * Complex.I) a (m : ℝ)‖ ≤
        2 * a ^ (-σ) / Real.pi * (Real.log y + 1) := by
  calc
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊y⌋₊,
        ‖weightedIntegralTail ((σ : ℂ) + (t : ℂ) * Complex.I) a (m : ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, 2 * a ^ (-σ) / (Real.pi * (m : ℝ)) := by
      apply Finset.sum_le_sum
      intro m hm
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
      exact norm_weightedIntegralTail_le hσ hmpos ha (hcut m hm)
    _ = (2 * a ^ (-σ) / Real.pi) * ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, 1 / (m : ℝ) := by
      simp only [div_eq_mul_inv, mul_inv, Finset.mul_sum, one_mul, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_reciprocals_floor_le hy) (by positivity)

/-- A single signed cutoff suffices uniformly for all positive integer frequencies. -/
theorem norm_sum_weightedIntegralTail_source {σ t a y : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (ha : 0 < a) (hy : 1 ≤ y) (hcut : t / Real.pi < a) :
    ‖∑ m ∈ Finset.Icc 1 ⌊y⌋₊,
      weightedIntegralTail ((σ : ℂ) + (t : ℂ) * Complex.I) a (m : ℝ)‖ ≤
        2 * a ^ (-σ) / Real.pi * (Real.log y + 1) := by
  apply norm_sum_weightedIntegralTail_le hσ ha hy
  intro m hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have ht := (div_lt_iff₀ Real.pi_pos).mp hcut
  have hprod := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmone Real.pi_pos.le) ha.le
  nlinarith

end DhimanKadiriQuesadaHerrera2026
