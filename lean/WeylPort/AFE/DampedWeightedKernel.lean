module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.UpperIntegralEstimate
public import WeylPort.AFE.ChiGammaFactor
public import WeylPort.Analytic.ComplexLaplace

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Actual damped weighted integrals and the existing Gamma–Laplace theorem

Directly consumes node-71 GuthMaynard/DFIComplexLaplace.lean, SHA-256
1f79e5847fb9cb9e3e3d1a61fa62f9043ecf9b362c643fc06f42730607473bf9.
No upstream code is copied or modified. Finite dominated convergence and a
damping-uniform oscillatory tail bound identify the actual improper integral.
No undamped whole-line Bochner integral is asserted.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex MeasureTheory
open scoped Topology

/-- The actual weighted kernel with positive exponential damping. -/
noncomputable def dampedWeightedKernel (s : ℂ) (ε m u : ℝ) : ℂ :=
  ((u : ℂ) ^ (-s) * exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))) *
    exp (-((ε : ℂ) * (u : ℂ)))

/-- The damping parameter acts continuously even at the totalized value u=0. -/
theorem continuous_dampedWeightedKernel_parameter (s : ℂ) (m u : ℝ) :
    Continuous (fun ε : ℝ => dampedWeightedKernel s ε m u) := by
  unfold dampedWeightedKernel
  fun_prop

/-- Every finite damped integral retains local integrability at the zero endpoint. -/
theorem intervalIntegrable_dampedWeightedKernel {s : ℂ} (hs : s.re < 1) (ε m a b : ℝ) :
    IntervalIntegrable (dampedWeightedKernel s ε m) volume a b := by
  exact (intervalIntegrable_weighted_integrand hs a b m).mul_continuousOn (by fun_prop)

/-- The actual kernel is exactly the existing complex Laplace integrand. -/
theorem dampedWeightedKernel_eq_laplace (s : ℂ) (ε m u : ℝ) :
    dampedWeightedKernel s ε m u =
      (u : ℂ) ^ ((1 - s) - 1) *
        exp (-(((ε : ℂ) - 2 * (Real.pi : ℂ) * I * (m : ℂ)) * (u : ℂ))) := by
  rw [show (1 - s) - 1 = -s by ring]
  unfold dampedWeightedKernel
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Positive damping gives absolute integrability on the positive half-line. -/
theorem integrableOn_dampedWeightedKernel {s : ℂ} (hs : s.re < 1)
    {ε : ℝ} (hε : 0 < ε) (m : ℝ) :
    IntegrableOn (dampedWeightedKernel s ε m) (Set.Ioi 0) := by
  have hz : 0 < (1 - s).re := by simp; linarith
  have ha : 0 < ((ε : ℂ) - 2 * (Real.pi : ℂ) * I * (m : ℂ)).re := by simpa using hε
  exact (RiemannZeta.GuthMaynard.integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi hz ha).congr_fun
    (fun u _ => (dampedWeightedKernel_eq_laplace s ε m u).symm) measurableSet_Ioi

/-- The already proved foundation Laplace theorem evaluates the actual damped integral. -/
theorem integral_dampedWeightedKernel_Ioi {s : ℂ} (hs : s.re < 1)
    {ε : ℝ} (hε : 0 < ε) (m : ℝ) :
    (∫ u in Set.Ioi 0, dampedWeightedKernel s ε m u) =
      ((ε : ℂ) - 2 * (Real.pi : ℂ) * I * (m : ℂ)) ^ (s - 1) * Gamma (1 - s) := by
  have hz : 0 < (1 - s).re := by simp; linarith
  have ha : 0 < ((ε : ℂ) - 2 * (Real.pi : ℂ) * I * (m : ℂ)).re := by simpa using hε
  simp_rw [dampedWeightedKernel_eq_laplace]
  simpa only [neg_sub, RiemannZeta.GuthMaynard.dfiComplexLaplace] using RiemannZeta.GuthMaynard.dfiComplexLaplace_eq hz ha

/-- The zero-damping value uses the actual principal branch at the negative imaginary axis. -/
theorem continuousAt_dampedGamma_factor (s : ℂ) {m : ℝ} (hm : 0 < m) :
    ContinuousAt (fun ε : ℝ =>
      ((ε : ℂ) - 2 * (Real.pi : ℂ) * I * (m : ℂ)) ^ (s - 1) * Gamma (1 - s)) 0 := by
  have hi : (0 : ℂ) - 2 * (Real.pi : ℂ) * I * (m : ℂ) ∈ Complex.slitPlane := by
    apply Or.inr
    have hp : Real.pi * m ≠ 0 := mul_ne_zero Real.pi_ne_zero hm.ne'
    simp only [sub_im, zero_im, mul_im, mul_re, ofReal_im, ofReal_re, I_im, I_re]
    norm_num
    positivity
  exact ((continuousAt_cpow_const (b := s - 1) hi).comp
    (f := fun ε : ℝ => (ε : ℂ) - 2 * (Real.pi : ℂ) * I * (m : ℂ))
    (Complex.continuous_ofReal.continuousAt.sub continuousAt_const)).mul_const _


/-- Zero damping returns the literal undamped weighted integrand. -/
theorem dampedWeightedKernel_zero (s : ℂ) (m u : ℝ) :
    dampedWeightedKernel s 0 m u =
      (u : ℂ) ^ (-s) * exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ)) := by
  simp [dampedWeightedKernel]

/-- Nonnegative damping contracts the norm on the positive half-line. -/
theorem norm_dampedWeightedKernel_le (s : ℂ) {ε u : ℝ} (hε : 0 ≤ ε) (hu : 0 ≤ u) (m : ℝ) :
    ‖dampedWeightedKernel s ε m u‖ ≤
      ‖(u : ℂ) ^ (-s) * exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))‖ := by
  rw [dampedWeightedKernel, norm_mul, Complex.norm_exp]
  apply mul_le_of_le_one_right (norm_nonneg _)
  apply Real.exp_le_one_iff.mpr
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact neg_nonpos.mpr (mul_nonneg hε hu)

/-- Dominated convergence removes damping on each actual finite zero-endpoint interval. -/
theorem dampedWeightedKernel_finite_abel_limit {s : ℂ} (hs : s.re < 1)
    {R : ℝ} (hR : 0 ≤ R) (m : ℝ) :
    Filter.Tendsto (fun ε : ℝ => ∫ u in 0..R, dampedWeightedKernel s ε m u)
      (𝓝[>] (0 : ℝ)) (𝓝 (weightedIntegral s 0 R m)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun u => ‖(u : ℂ) ^ (-s) * exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))‖)
  · apply Filter.Eventually.of_forall
    intro ε
    rw [Set.uIoc_of_le hR]
    exact (intervalIntegrable_dampedWeightedKernel hs ε m 0 R).1.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    apply Filter.Eventually.of_forall
    intro u hu
    rw [Set.uIoc_of_le hR] at hu
    exact norm_dampedWeightedKernel_le s hε.le hu.1.le m
  · exact (intervalIntegrable_weighted_integrand hs 0 R m).norm
  · apply Filter.Eventually.of_forall
    intro u _
    simpa only [dampedWeightedKernel_zero] using
      (continuous_dampedWeightedKernel_parameter s m u).continuousAt.tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)

/-- The finite upper tail is bounded independently of the nonnegative damping parameter. -/
theorem norm_integral_dampedWeightedKernel_le {σ t ε m a b : ℝ} (hσ : 0 ≤ σ)
    (hε : 0 ≤ ε) (hm : 0 < m) (ha : 0 < a) (hab : a ≤ b)
    (hcut : t < Real.pi * m * a) :
    ‖∫ u in a..b, dampedWeightedKernel ((σ : ℂ) + (t : ℂ) * I) ε m u‖ ≤
      2 * a ^ (-σ) / (Real.pi * m) := by
  have hp (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < u := ha.trans_le hu.1
  let g : ℝ → ℝ := fun u => u ^ (-σ) * Real.exp (-ε * u)
  let g' : ℝ → ℝ := fun u =>
    (-σ * u ^ (-σ - 1)) * Real.exp (-ε * u) +
      u ^ (-σ) * (Real.exp (-ε * u) * (-ε))
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) : HasDerivAt g (g' u) u := by
    dsimp only [g, g']
    simpa only [id_eq, mul_one] using
      (Real.hasDerivAt_rpow_const (p := -σ) (Or.inl (hp u hu).ne')).fun_mul
        (((hasDerivAt_id u).const_mul (-ε)).exp)
  have hgc : ContinuousOn g' (Set.Icc a b) := by
    intro u hu
    have h1 := Real.continuousAt_rpow_const u (-σ - 1) (Or.inl (hp u hu).ne')
    have h2 := Real.continuousAt_rpow_const u (-σ) (Or.inl (hp u hu).ne')
    exact ((continuousAt_const.mul h1).mul (by fun_prop) |>.add
      (h2.mul ((by fun_prop : ContinuousAt (fun v : ℝ => Real.exp (-ε * v)) u).mul
        continuousAt_const))).continuousWithinAt
  have hgn (u : ℝ) (hu : u ∈ Set.Icc a b) : g' u ≤ 0 := by
    dsimp [g']
    apply add_nonpos
    · exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ)
          (Real.rpow_nonneg (hp u hu).le _)) (Real.exp_nonneg _)
    · exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hp u hu).le _)
        (mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (neg_nonpos.mpr hε))
  have h := norm_integral_mul_le_of_primitive_bound hab hd
    (F := fun v => ∫ u in a..v, exp (I * (weightedIntegralPhase t m u : ℂ)))
    (fun u hu => upper_phase_primitive_hasDerivAt t m ha (hp u hu)) hgc
    ((continuousOn_upper_phase t m).mono (fun u hu => hp u hu))
    (mul_nonneg (Real.rpow_nonneg (hp b (Set.right_mem_Icc.mpr hab)).le _)
      (Real.exp_nonneg _)) hgn (by simp)
    (fun u hu => norm_integral_upper_phase_le hm ha hu.1 hcut)
  have he : (∫ u in a..b, dampedWeightedKernel ((σ : ℂ) + (t : ℂ) * I) ε m u) =
      ∫ u in a..b, (g u : ℂ) * exp (I * (weightedIntegralPhase t m u : ℂ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hup : 0 < u := hp u (Set.uIcc_of_le hab ▸ hu)
    unfold dampedWeightedKernel
    rw [show -((σ : ℂ) + (t : ℂ) * I) =
      (((-σ : ℝ) : ℂ) - (t : ℂ) * I) by push_cast; ring]
    rw [cpow_linear_wave_eq_power_log_phase (-σ) t m hup]
    dsimp [g]
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    rw [neg_mul]
    ring
  rw [he]
  apply h.trans
  have hg : g a ≤ a ^ (-σ) := by
    apply mul_le_of_le_one_right (Real.rpow_nonneg ha.le _)
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) ha.le
  calc
    g a * (2 / (Real.pi * m)) ≤ a ^ (-σ) * (2 / (Real.pi * m)) :=
      mul_le_mul_of_nonneg_right hg (by positivity)
    _ = _ := by ring

/-- Positive damping permits passage of the uniform finite bound to the Lebesgue tail. -/
theorem norm_integral_Ioi_dampedWeightedKernel_le {σ t ε m a : ℝ}
    (hσ : σ ∈ Set.Ico 0 1) (hε : 0 < ε) (hm : 0 < m) (ha : 0 < a)
    (hcut : t < Real.pi * m * a) :
    ‖∫ u in Set.Ioi a, dampedWeightedKernel ((σ : ℂ) + (t : ℂ) * I) ε m u‖ ≤
      2 * a ^ (-σ) / (Real.pi * m) := by
  have hs : ((σ : ℂ) + (t : ℂ) * I).re < 1 := by simpa using hσ.2
  have hi := (integrableOn_dampedWeightedKernel hs hε m).mono_set
    (Set.Ioi_subset_Ioi ha.le)
  have hlim := intervalIntegral_tendsto_integral_Ioi a hi Filter.tendsto_id
  apply le_of_tendsto hlim.norm
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  exact norm_integral_dampedWeightedKernel_le hσ.1 hε.le hm ha hb hcut

/-- The exact damped Gamma evaluation has a truncation error uniform as damping vanishes. -/
theorem norm_dampedGamma_sub_finite_integral_le {σ t ε m R : ℝ}
    (hσ : σ ∈ Set.Ico 0 1) (hε : 0 < ε) (hm : 0 < m) (hR : 0 < R)
    (hcut : t < Real.pi * m * R) :
    ‖((ε : ℂ) - 2 * (Real.pi : ℂ) * I * (m : ℂ)) ^
        (((σ : ℂ) + (t : ℂ) * I) - 1) * Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)) -
      ∫ u in 0..R, dampedWeightedKernel ((σ : ℂ) + (t : ℂ) * I) ε m u‖ ≤
      2 * R ^ (-σ) / (Real.pi * m) := by
  have hs : ((σ : ℂ) + (t : ℂ) * I).re < 1 := by simpa using hσ.2
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi
    (integrableOn_dampedWeightedKernel hs hε m) hR.le
  rw [integral_dampedWeightedKernel_Ioi hs hε m] at hsplit
  have he : ((ε : ℂ) - 2 * (Real.pi : ℂ) * I * (m : ℂ)) ^
        (((σ : ℂ) + (t : ℂ) * I) - 1) * Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)) -
      (∫ u in 0..R, dampedWeightedKernel ((σ : ℂ) + (t : ℂ) * I) ε m u) =
      ∫ u in Set.Ioi R, dampedWeightedKernel ((σ : ℂ) + (t : ℂ) * I) ε m u := by
    linear_combination hsplit
  rw [he]
  exact norm_integral_Ioi_dampedWeightedKernel_le hσ hε hm hR hcut

/-- Abel passage preserves the actual finite integral and the explicit Gamma truncation error. -/
theorem norm_gamma_sub_weightedIntegral_le {σ t m R : ℝ} (hσ : σ ∈ Set.Ico 0 1)
    (hm : 0 < m) (hR : 0 < R) (hcut : t < Real.pi * m * R) :
    ‖(-(2 * (Real.pi : ℂ) * I * (m : ℂ))) ^ (((σ : ℂ) + (t : ℂ) * I) - 1) *
        Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)) -
      weightedIntegral ((σ : ℂ) + (t : ℂ) * I) 0 R m‖ ≤
      2 * R ^ (-σ) / (Real.pi * m) := by
  have hs : ((σ : ℂ) + (t : ℂ) * I).re < 1 := by simpa using hσ.2
  have hg := (continuousAt_dampedGamma_factor ((σ : ℂ) + (t : ℂ) * I) hm).tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
  have hf := dampedWeightedKernel_finite_abel_limit hs hR.le m
  apply le_of_tendsto (by simpa only [ofReal_zero, zero_sub] using (hg.sub hf).norm)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact norm_dampedGamma_sub_finite_integral_le hσ hε hm hR hcut

/-- The actual conditionally convergent positive-frequency integral equals its principal-branch Gamma value. -/
theorem weightedIntegralTail_zero_eq_gamma {σ t m : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hm : 0 < m) :
    weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 m =
      (-(2 * (Real.pi : ℂ) * I * (m : ℂ))) ^ (((σ : ℂ) + (t : ℂ) * I) - 1) *
        Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)) := by
  have hdecay : Filter.Tendsto (fun R : ℝ => 2 * R ^ (-σ) / (Real.pi * m))
      Filter.atTop (𝓝 0) := by
    simpa only [mul_zero, zero_div] using
      (tendsto_rpow_neg_atTop hσ.1).const_mul 2 |>.div_const (Real.pi * m)
  have hbound : ∀ᶠ R : ℝ in Filter.atTop,
      ‖(-(2 * (Real.pi : ℂ) * I * (m : ℂ))) ^ (((σ : ℂ) + (t : ℂ) * I) - 1) *
          Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)) -
        weightedIntegral ((σ : ℂ) + (t : ℂ) * I) 0 R m‖ ≤
        2 * R ^ (-σ) / (Real.pi * m) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
      Filter.eventually_gt_atTop (t / (Real.pi * m))] with R hR hcut
    apply norm_gamma_sub_weightedIntegral_le ⟨hσ.1.le, hσ.2⟩ hm hR
    have hc := (div_lt_iff₀ (show 0 < Real.pi * m by positivity)).mp hcut
    nlinarith
  have hlim := ((weightedIntegral_tendsto_tail (t := t) hσ hm 0).const_sub
    ((-(2 * (Real.pi : ℂ) * I * (m : ℂ))) ^ (((σ : ℂ) + (t : ℂ) * I) - 1) *
      Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)))).norm
  have hz := le_of_tendsto_of_tendsto hlim hdecay hbound
  exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))).symm

/-- Positive frequency scaling does not cross the principal logarithm's branch cut. -/
theorem cpow_negative_imaginary_frequency (s : ℂ) {m : ℝ} (hm : 0 < m) :
    (-(2 * (Real.pi : ℂ) * I * (m : ℂ))) ^ (s - 1) =
      (2 * (Real.pi : ℂ) / I) ^ (s - 1) * (m : ℂ) ^ (s - 1) := by
  have hb : 2 * (Real.pi : ℂ) / I ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  have hm' : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hm.ne'
  have he : -(2 * (Real.pi : ℂ) * I * (m : ℂ)) = (2 * (Real.pi : ℂ) / I) * m := by
    rw [div_eq_mul_inv, inv_I]
    ring
  rw [he, cpow_def_of_ne_zero (mul_ne_zero hb hm'), log_mul_ofReal m hm _ hb,
    add_mul, exp_add, cpow_def_of_ne_zero hb, cpow_def_of_ne_zero hm', ofReal_log hm.le]
  exact mul_comm _ _

/-- The source Gamma evaluation is obtained from the proved improper limit with exact frequency scaling. -/
theorem weightedIntegralTail_zero_eq_gamma_product {σ t m : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hm : 0 < m) :
    weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 m =
      Gamma (1 - ((σ : ℂ) + (t : ℂ) * I)) *
        (2 * (Real.pi : ℂ) / I) ^ (((σ : ℂ) + (t : ℂ) * I) - 1) *
        (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1) := by
  rw [weightedIntegralTail_zero_eq_gamma hσ hm, cpow_negative_imaginary_frequency _ hm]
  ring

/-- The actual positive-frequency main integral consumes Lemma 7's relative-error identity. -/
theorem weightedIntegralTail_zero_eq_chi {σ t m t₀ : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hm : 0 < m) (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 m =
      chi ((σ : ℂ) + (t : ℂ) * I) *
        (1 + gammaChiError ((σ : ℂ) + (t : ℂ) * I)) *
        (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1) := by
  rw [weightedIntegralTail_zero_eq_gamma_product hσ hm,
    gamma_factor_eq_chi_mul_one_add ht₀ (by simpa using ht)]

/-- Splitting at a finite cutoff is valid for the actual conditionally convergent improper integral. -/
theorem weightedIntegralTail_eq_sub {σ t m : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hm : 0 < m) (a : ℝ) :
    weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) a m =
      weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 m -
        weightedIntegral ((σ : ℂ) + (t : ℂ) * I) 0 a m := by
  have hs : ((σ : ℂ) + (t : ℂ) * I).re < 1 := by simpa using hσ.2
  apply tendsto_nhds_unique (weightedIntegral_tendsto_tail hσ hm a)
  have h := (weightedIntegral_tendsto_tail (t := t) hσ hm 0).sub_const
    (weightedIntegral ((σ : ℂ) + (t : ℂ) * I) 0 a m)
  simpa only [weightedIntegral_sub hs] using h

/-- The three-term decomposition used in the AFE is an exact identity of actual integrals. -/
theorem weightedIntegral_eq_tail_sub_lower_sub_upper {σ t m : ℝ}
    (hσ : σ ∈ Set.Ioo 0 1) (hm : 0 < m) (x R : ℝ) :
    weightedIntegral ((σ : ℂ) + (t : ℂ) * I) x R m =
      weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 m -
        weightedIntegral ((σ : ℂ) + (t : ℂ) * I) 0 x m -
        weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) R m := by
  have hs : ((σ : ℂ) + (t : ℂ) * I).re < 1 := by simpa using hσ.2
  rw [weightedIntegralTail_eq_sub hσ hm R]
  linear_combination -(weightedIntegral_sub hs 0 R x m)

end DhimanKadiriQuesadaHerrera2026
