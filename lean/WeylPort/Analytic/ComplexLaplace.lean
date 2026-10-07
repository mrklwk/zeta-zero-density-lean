module
public import WeylPort.Analytic.RealLaplace
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

-- Lean 4.34 elaborator compatibility; kernel checking stays enabled.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Complex Gamma--Laplace integral for the DFI Neumann kernel

The oscillatory part of Schläfli's representation is handled by Abel
regularization.  This module proves the complex-damping Gamma integral on
the full right half-plane.  The proof differentiates under the integral and
uses analytic continuation from positive real damping parameters.
-/

open Complex Set MeasureTheory Filter
open scoped Topology

namespace RiemannZeta.GuthMaynard

theorem integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi
    {s a : ℂ} (hs : 0 < s.re) (ha : 0 < a.re) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (s - 1) * cexp (-(a * x))) (Set.Ioi 0) := by
  have hbase := integrableOn_cpow_mul_exp_neg_mul_Ioi hs ha
  refine hbase.norm.mono' ?_ ?_
  · have hcont : ContinuousOn (fun x : ℝ =>
        (x : ℂ) ^ (s - 1) * cexp (-(a * x))) (Set.Ioi 0) := by
      intro x hx
      apply ContinuousAt.continuousWithinAt
      exact (Complex.continuousAt_ofReal_cpow_const x (s - 1)
        (Or.inr hx.ne')).mul (Complex.continuous_exp.continuousAt.comp (by fun_prop))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp]
    simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
    exact le_rfl

/-- The `dfiComplexLaplace` definition used by the source-facing construction in `DFIComplexLaplace`. -/
noncomputable def dfiComplexLaplace (s a : ℂ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 0, (x : ℂ) ^ (s - 1) * cexp (-(a * x))

theorem hasDerivAt_dfiComplexLaplace
    {s a : ℂ} (hs : 0 < s.re) (ha : 0 < a.re) :
    HasDerivAt (dfiComplexLaplace s)
      (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (-x) * cexp (-(a * x))) a := by
  let F : ℂ → ℝ → ℂ := fun b x =>
    (x : ℂ) ^ (s - 1) * cexp (-(b * x))
  let F' : ℂ → ℝ → ℂ := fun b x =>
    (x : ℂ) ^ (s - 1) * (-x) * cexp (-(b * x))
  let r : ℝ := a.re / 2
  have hr : 0 < r := half_pos ha
  have hball : Metric.ball a r ∈ 𝓝 a := Metric.ball_mem_nhds a hr
  have hMeas : ∀ᶠ b in 𝓝 a,
      AEStronglyMeasurable (F b) (volume.restrict (Set.Ioi 0)) := by
    filter_upwards with b
    have hcont : ContinuousOn (F b) (Set.Ioi 0) := by
      intro x hx
      apply ContinuousAt.continuousWithinAt
      exact (Complex.continuousAt_ofReal_cpow_const x (s - 1)
        (Or.inr hx.ne')).mul (Complex.continuous_exp.continuousAt.comp (by fun_prop))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hFInt : Integrable (F a) (volume.restrict (Set.Ioi 0)) := by
    exact integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi hs ha
  have hF'Meas : AEStronglyMeasurable (F' a)
      (volume.restrict (Set.Ioi 0)) := by
    have hcont : ContinuousOn (F' a) (Set.Ioi 0) := by
      intro x hx
      apply ContinuousAt.continuousWithinAt
      exact ((Complex.continuousAt_ofReal_cpow_const x (s - 1)
        (Or.inr hx.ne')).mul (by fun_prop)).mul
          (Complex.continuous_exp.continuousAt.comp (by fun_prop))
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  let bound : ℝ → ℝ := fun x => x ^ s.re * Real.exp (-(r * x))
  have hBoundInt : Integrable bound (volume.restrict (Set.Ioi 0)) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := (1 : ℝ)) (s := s.re) (b := r) (by linarith) (by norm_num) hr
    change IntegrableOn bound (Set.Ioi 0)
    simpa only [bound, neg_mul, Real.rpow_one] using h
  have hBound : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ∀ b ∈ Metric.ball a r, ‖F' b x‖ ≤ bound x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    intro b hb
    have hx0 : 0 < x := hx
    have hbre : r ≤ b.re := by
      have hre : |b.re - a.re| < r :=
        (abs_re_le_norm (b - a)).trans_lt (by simpa [dist_eq_norm] using hb)
      dsimp [r]
      have hlower := (abs_lt.mp hre).1
      dsimp [r] at hlower
      linarith
    dsimp [F', bound]
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
      norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0,
      Complex.norm_exp]
    simp only [sub_re, one_re, neg_re, mul_re, ofReal_re, ofReal_im,
      mul_zero, sub_zero]
    have hexp : Real.exp (-(b.re * x)) ≤ Real.exp (-(r * x)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    rw [show x ^ (s.re - 1) * x = x ^ s.re by
      calc
        x ^ (s.re - 1) * x = x ^ (s.re - 1) * x ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = x ^ ((s.re - 1) + 1) := (Real.rpow_add hx0 _ _).symm
        _ = x ^ s.re := by congr 1; ring]
    exact mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hx0.le _)
  have hDiff : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ∀ b ∈ Metric.ball a r, HasDerivAt (F · x) (F' b x) b := by
    filter_upwards with x
    intro b _
    dsimp [F, F']
    convert (Complex.hasDerivAt_exp (-(b * x))).comp b
      (((hasDerivAt_id b).mul_const (x : ℂ)).neg) |>.const_mul
        ((x : ℂ) ^ (s - 1)) using 1
    · funext z; dsimp
    · ring
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0)) (bound := bound)
    (F := F) (F' := F') hball hMeas hFInt hF'Meas hBound hBoundInt hDiff
  exact h.2

theorem analyticOnNhd_dfiComplexLaplace {s : ℂ} (hs : 0 < s.re) :
    AnalyticOnNhd ℂ (dfiComplexLaplace s) {a : ℂ | 0 < a.re} := by
  have hopen : IsOpen {a : ℂ | 0 < a.re} :=
    isOpen_lt continuous_const continuous_re
  apply (show DifferentiableOn ℂ (dfiComplexLaplace s) {a : ℂ | 0 < a.re} by
    intro a ha
    exact (hasDerivAt_dfiComplexLaplace hs ha).differentiableAt.differentiableWithinAt
    ).analyticOnNhd hopen

theorem dfiComplexLaplace_ofReal
    {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    dfiComplexLaplace s (r : ℂ) = (r : ℂ) ^ (-s) * Gamma s := by
  have h := integral_cpow_mul_exp_neg_mul_Ioi_eq hs hr
  unfold dfiComplexLaplace
  rw [show (∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ (s - 1) * cexp (-((r : ℂ) * x))) =
      ∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * cexp (-(r * x)) by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    push_cast
    rfl]
  rw [h]
  congr 1
  rw [one_div, Complex.inv_cpow]
  · rw [Complex.cpow_neg]
  · rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm

theorem dfiComplexLaplace_eq
    {s a : ℂ} (hs : 0 < s.re) (ha : 0 < a.re) :
    dfiComplexLaplace s a = a ^ (-s) * Gamma s := by
  let U : Set ℂ := {b : ℂ | 0 < b.re}
  let F : ℂ → ℂ := dfiComplexLaplace s
  let G : ℂ → ℂ := fun b => b ^ (-s) * Gamma s
  have hF : AnalyticOnNhd ℂ F U := by
    simpa only [F, U] using analyticOnNhd_dfiComplexLaplace hs
  have hGDiff : DifferentiableOn ℂ G U := by
    intro b hb
    have hbpos : 0 < b.re := hb
    dsimp [G]
    exact ((differentiableAt_id.cpow_const
      (Complex.mem_slitPlane_iff.mpr (Or.inl hbpos))).mul
        (differentiableAt_const (c := Gamma s))).differentiableWithinAt
  have hUOpen : IsOpen U := by
    dsimp [U]
    exact isOpen_lt continuous_const continuous_re
  have hG : AnalyticOnNhd ℂ G U := hGDiff.analyticOnNhd hUOpen
  have hReal : ∃ᶠ (x : ℝ) in 𝓝[≠] (1 : ℝ), F x = G x := by
    have hEventually : ∀ᶠ x : ℝ in 𝓝 (1 : ℝ), F x = G x := by
      filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with x hx
      exact dfiComplexLaplace_ofReal hs hx
    have hEventually' : ∀ᶠ x : ℝ in 𝓝[≠] (1 : ℝ), F x = G x :=
      hEventually.filter_mono inf_le_left
    exact hEventually'.frequently
  have hFreq : ∃ᶠ b : ℂ in 𝓝[≠] (1 : ℂ), F b = G b := by
    rw [frequently_iff_seq_forall] at hReal ⊢
    obtain ⟨xs, hxs, hxEq⟩ := hReal
    refine ⟨fun n => (xs n : ℂ), ?_, fun n => ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hxs ⊢
      constructor
      · simpa only [Function.comp_def, Complex.ofReal_one] using Complex.continuous_ofReal.continuousAt.tendsto.comp hxs.1
      · simpa using hxs.2
    · simpa [F, G] using hxEq n
  have hEq := hF.eqOn_of_preconnected_of_frequently_eq hG
    (convex_halfSpace_re_gt 0).isPreconnected
    (z₀ := (1 : ℂ)) (by simp [U]) hFreq
  exact hEq ha

end RiemannZeta.GuthMaynard
