module
/-
Adapted from Scott McColm's ZetaBounds.lean at
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be; MIT.
See third_party/mccolm/ANALYTIC_SOURCE_IMPORTS.json for the port boundary.
-/
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.JensenFormula

@[expose] public section

open Complex Filter Set MeasureTheory Asymptotics
open scoped Topology

set_option autoImplicit false

namespace MathCollab.Density.ZetaGrowth

/-- The bounded fractional-part kernel used in Abel's integral continuation of zeta.
It is cut off below one so its Mellin transform has no singularity at zero. -/
noncomputable def abelZetaKernel (x : ℝ) : ℂ :=
  if 1 < x then ((Int.fract x : ℝ) : ℂ) else 0

theorem abelZetaKernel_eq_of_one_lt {x : ℝ} (hx : 1 < x) :
    abelZetaKernel x = ((Int.fract x : ℝ) : ℂ) := by
  simp [abelZetaKernel, hx]

theorem abelZetaKernel_eq_zero_of_le_one {x : ℝ} (hx : x ≤ 1) :
    abelZetaKernel x = 0 := by
  simp [abelZetaKernel, not_lt.mpr hx]

theorem norm_abelZetaKernel_le_one (x : ℝ) : ‖abelZetaKernel x‖ ≤ 1 := by
  by_cases hx : 1 < x
  · rw [abelZetaKernel_eq_of_one_lt hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg x)]
    exact (Int.fract_lt_one x).le
  · rw [abelZetaKernel_eq_zero_of_le_one (not_lt.mp hx), norm_zero]
    norm_num

theorem measurable_abelZetaKernel : Measurable abelZetaKernel := by
  apply Measurable.ite measurableSet_Ioi
  · exact Complex.measurable_ofReal.comp measurable_fract
  · exact measurable_const

theorem locallyIntegrableOn_abelZetaKernel :
    LocallyIntegrableOn abelZetaKernel (Ioi 0) := by
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k hk hkCompact
  apply IntegrableOn.of_bound hkCompact.measure_lt_top
  · exact measurable_abelZetaKernel.aestronglyMeasurable.restrict
  · filter_upwards with x
    exact norm_abelZetaKernel_le_one x

theorem abelZetaKernel_isBigO_atTop :
    abelZetaKernel =O[atTop] (fun x : ℝ => x ^ (0 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [Real.rpow_zero, norm_one, one_mul]
  exact norm_abelZetaKernel_le_one x

theorem abelZetaKernel_isBigO_zero (b : ℝ) :
    abelZetaKernel =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-b)) := by
  apply IsBigO.of_bound 1
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
  rw [abelZetaKernel_eq_zero_of_le_one hx.2.le, norm_zero]
  positivity

/-- Abel's remainder integral, represented as a Mellin transform. -/
noncomputable def abelZetaRemainder (s : ℂ) : ℂ :=
  mellin abelZetaKernel (-s)

theorem differentiableAt_abelZetaRemainder {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ abelZetaRemainder s := by
  unfold abelZetaRemainder
  have hMellin : DifferentiableAt ℂ (mellin abelZetaKernel) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
      locallyIntegrableOn_abelZetaKernel (by simpa using abelZetaKernel_isBigO_atTop)
      (by simpa using hs) (abelZetaKernel_isBigO_zero (-s.re - 1)) (by simp)
  exact hMellin.comp s (hasDerivAt_neg s).differentiableAt

theorem mellinConvergent_abelZetaKernel {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent abelZetaKernel (-s) :=
  mellinConvergent_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    locallyIntegrableOn_abelZetaKernel (by simpa using abelZetaKernel_isBigO_atTop)
    (by simpa using hs) (abelZetaKernel_isBigO_zero (-s.re - 1)) (by simp)

/-- Abel's Mellin remainder is the usual fractional-part integral over `(1, ∞)`. -/
theorem abelZetaRemainder_eq_integral {s : ℂ} (hs : 0 < s.re) :
    abelZetaRemainder s =
      ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (-s - 1) * abelZetaKernel t
  have hF : IntegrableOn F (Ioi (0 : ℝ)) := by
    simpa [MellinConvergent, F, smul_eq_mul] using mellinConvergent_abelZetaKernel hs
  have hFleft : IntegrableOn F (Ioc (0 : ℝ) 1) :=
    hF.mono_set (Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi (by norm_num)))
  have hFright : IntegrableOn F (Ioi (1 : ℝ)) :=
    hF.mono_set (Ioi_subset_Ioi (by norm_num))
  rw [abelZetaRemainder, mellin]
  change (∫ t in Ioi (0 : ℝ), F t) = _
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num),
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hFleft hFright]
  have hLeft : ∫ t in Ioc (0 : ℝ) 1, F t = 0 := by
    rw [show (∫ t in Ioc (0 : ℝ) 1, F t) = ∫ _t in Ioc (0 : ℝ) 1, (0 : ℂ) by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      simp [F, abelZetaKernel_eq_zero_of_le_one ht.2]]
    simp
  rw [hLeft, zero_add]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only [F]
  rw [abelZetaKernel_eq_of_one_lt ht]
  rw [mul_comm]
  congr 1
  ring_nf

theorem integrableOn_abelZetaRemainder_integrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn
      (fun t : ℝ => ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
      (Ioi (1 : ℝ)) := by
  have hF : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (-s - 1) * abelZetaKernel t) (Ioi (0 : ℝ)) := by
    simpa [MellinConvergent, smul_eq_mul] using mellinConvergent_abelZetaKernel hs
  have hF' := hF.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  rw [integrableOn_congr_fun (s := Ioi (1 : ℝ)) (g := fun t : ℝ =>
      (t : ℂ) ^ (-s - 1) * abelZetaKernel t) (fun t ht => by
        dsimp only
        rw [abelZetaKernel_eq_of_one_lt ht, mul_comm]
        congr 1
        ring_nf) measurableSet_Ioi]
  exact hF'

/-- The pole-removed zeta function, with its removable value filled in at one. -/
noncomputable def regularizedRiemannZeta (s : ℂ) : ℂ :=
  Function.update (fun z => (z - 1) * riemannZeta z) 1 1 s

/-- The holomorphic Abel-continuation expression on `Re(s) > 0`. -/
noncomputable def regularizedAbelZeta (s : ℂ) : ℂ :=
  s - s * (s - 1) * abelZetaRemainder s

theorem differentiableAt_regularizedRiemannZeta (s : ℂ) :
    DifferentiableAt ℂ regularizedRiemannZeta s := by
  change DifferentiableAt ℂ
    (Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1) s
  by_cases hs : s = 1
  · subst s
    refine (analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_ ?_).differentiableAt
    · filter_upwards [self_mem_nhdsWithin] with z hz
      have hbase : DifferentiableAt ℂ (fun w : ℂ => (w - 1) * riemannZeta w) z :=
        (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz)
      apply hbase.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hz] with w hw
      simpa using Function.update_of_ne (f := fun w : ℂ => (w - 1) * riemannZeta w)
        (v := (1 : ℂ)) hw
    · rw [continuousAt_update_same]
      exact riemannZeta_residue_one
  · have hbase : DifferentiableAt ℂ (fun w : ℂ => (w - 1) * riemannZeta w) s :=
      (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs)
    apply hbase.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hs] with w hw
    simpa using Function.update_of_ne (f := fun w : ℂ => (w - 1) * riemannZeta w)
      (v := (1 : ℂ)) hw

theorem differentiableAt_regularizedAbelZeta {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ regularizedAbelZeta s := by
  unfold regularizedAbelZeta
  exact differentiableAt_id.sub
    ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
      (differentiableAt_abelZetaRemainder hs))

theorem sum_one_Icc (n : ℕ) :
    ∑ _k ∈ Finset.Icc 1 n, (1 : ℂ) = n := by
  simp

theorem sum_one_Icc_isBigO :
    (fun n : ℕ => ∑ _k ∈ Finset.Icc 1 n, (1 : ℂ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards with n
  simp

theorem natFloor_cast_complex (t : ℝ) (ht : 1 < t) :
    ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
  have hfloor : (⌊t⌋₊ : ℝ) = t - Int.fract t := by
    rw [natCast_floor_eq_intCast_floor (zero_le_one.trans ht.le)]
    linarith [Int.floor_add_fract t]
  exact_mod_cast hfloor

theorem integral_Ioi_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s)) = 1 / (s - 1) := by
  rw [integral_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one]
  simp only [ofReal_one, one_cpow]
  rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]

theorem riemannZeta_eq_abel_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s * (1 / (s - 1) - abelZetaRemainder s) := by
  have hSeries := LSeries_eq_mul_integral (1 : ℕ → ℂ) zero_le_one hs
    (LSeriesSummable_one_iff.mpr hs) sum_one_Icc_isBigO
  rw [LSeries_one_eq_riemannZeta hs] at hSeries
  have hPower : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_cpow_of_lt (by simp; linarith) zero_lt_one
  have hRemainder := integrableOn_abelZetaRemainder_integrand (zero_lt_one.trans hs)
  rw [hSeries]
  congr 1
  calc
    (∫ t in Ioi (1 : ℝ),
        (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, (1 : ℂ)) * (t : ℂ) ^ (-(s + 1))) =
        ∫ t in Ioi (1 : ℝ),
          ((t : ℂ) ^ (-s) - ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [sum_one_Icc, natFloor_cast_complex t ht, sub_mul]
      congr 1
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt (zero_lt_one.trans ht))
      calc
        (t : ℂ) * (t : ℂ) ^ (-(s + 1)) =
            (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [cpow_one]
        _ = (t : ℂ) ^ ((1 : ℂ) + (-(s + 1))) := (cpow_add _ _ ht0).symm
        _ = (t : ℂ) ^ (-s) := by congr 1; ring
    _ = (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-s)) -
        ∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
      rw [integral_sub hPower hRemainder]
    _ = 1 / (s - 1) - abelZetaRemainder s := by
      rw [integral_Ioi_cpow_neg hs, abelZetaRemainder_eq_integral (zero_lt_one.trans hs)]

theorem regularized_zeta_eq_abel_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    regularizedRiemannZeta s = regularizedAbelZeta s := by
  have hs1 : s ≠ 1 := ne_of_apply_ne re (by simp; linarith)
  rw [regularizedRiemannZeta, Function.update_of_ne hs1, regularizedAbelZeta,
    riemannZeta_eq_abel_of_one_lt_re hs]
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp [hsub]

/-- Abel's expression analytically continues the pole-removed zeta function throughout
the right half-plane. -/
theorem regularized_zeta_eq_abel {s : ℂ} (hs : 0 < s.re) :
    regularizedRiemannZeta s = regularizedAbelZeta s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hUOpen : IsOpen U := isOpen_lt continuous_const continuous_re
  have hZetaDiff : DifferentiableOn ℂ regularizedRiemannZeta U := fun z _hz =>
    (differentiableAt_regularizedRiemannZeta z).differentiableWithinAt
  have hZeta : AnalyticOnNhd ℂ regularizedRiemannZeta U :=
    hZetaDiff.analyticOnNhd hUOpen
  have hAbelDiff : DifferentiableOn ℂ regularizedAbelZeta U := fun z hz =>
    (differentiableAt_regularizedAbelZeta hz).differentiableWithinAt
  have hAbel : AnalyticOnNhd ℂ regularizedAbelZeta U :=
    hAbelDiff.analyticOnNhd hUOpen
  have hEventually : regularizedRiemannZeta =ᶠ[𝓝 (2 : ℂ)] regularizedAbelZeta := by
    have hOpen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const continuous_re
    filter_upwards [hOpen.mem_nhds (by norm_num : (2 : ℂ) ∈ {z : ℂ | 1 < z.re})] with z hz
    exact regularized_zeta_eq_abel_of_one_lt_re hz
  exact hZeta.eqOn_of_preconnected_of_eventuallyEq hAbel
    (convex_halfSpace_re_gt 0).isPreconnected (by change (0 : ℝ) < 2; norm_num) hEventually hs

/-- Abel's integral formula for zeta in `Re(s) > 0`, away from its pole. -/
theorem riemannZeta_eq_abel {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = s / (s - 1) - s * abelZetaRemainder s := by
  have h := regularized_zeta_eq_abel hs
  rw [regularizedRiemannZeta, Function.update_of_ne hs1, regularizedAbelZeta] at h
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp [hsub] at h ⊢
  linear_combination h

/-- The fractional-part remainder in Abel's zeta formula is at most `1 / Re(s)`. -/
theorem norm_abelZetaRemainder_le {s : ℂ} (hs : 0 < s.re) :
    ‖abelZetaRemainder s‖ ≤ 1 / s.re := by
  have hInt := integrableOn_abelZetaRemainder_integrand hs
  have hPower : IntegrableOn (fun t : ℝ => t ^ (-s.re - 1)) (Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
  rw [abelZetaRemainder_eq_integral hs]
  calc
    ‖∫ t in Ioi (1 : ℝ), ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤
        ∫ t in Ioi (1 : ℝ), ‖((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (1 : ℝ), t ^ (-s.re - 1) := by
      apply setIntegral_mono_on hInt.norm hPower measurableSet_Ioi
      intro t ht
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg t),
        norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans ht)]
      change Int.fract t * t ^ (-(s.re + 1)) ≤ t ^ (-s.re - 1)
      rw [show -(s.re + 1) = -s.re - 1 by ring]
      have hpow : 0 ≤ t ^ (-s.re - 1) := Real.rpow_nonneg (zero_lt_one.trans ht).le _
      exact mul_le_of_le_one_left hpow (Int.fract_lt_one t).le
    _ = 1 / s.re := by
      rw [integral_Ioi_rpow_of_lt (by linarith) zero_lt_one, Real.one_rpow]
      rw [show -s.re - 1 + 1 = -s.re by ring, neg_div_neg_eq]

/-- A deliberately coarse pointwise zeta bound in the pole-free part of the right half-plane.
It is tailored to the Jensen discs used in the zero-count argument. -/
theorem norm_riemannZeta_le_five_mul_norm {s : ℂ} (hre : (1 / 4 : ℝ) ≤ s.re)
    (him : 1 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ 5 * ‖s‖ := by
  have hrePos : 0 < s.re := lt_of_lt_of_le (by norm_num) hre
  have hs1 : s ≠ 1 := by
    intro h
    subst s
    norm_num at him
  have hDen : 1 ≤ ‖s - 1‖ := by
    calc
      1 ≤ |(s - 1).im| := by simpa using him
      _ ≤ ‖s - 1‖ := abs_im_le_norm _
  have hRem : ‖abelZetaRemainder s‖ ≤ 4 := by
    calc
      ‖abelZetaRemainder s‖ ≤ 1 / s.re := norm_abelZetaRemainder_le hrePos
      _ ≤ 4 := (div_le_iff₀ hrePos).2 (by nlinarith)
  rw [riemannZeta_eq_abel hrePos hs1]
  calc
    ‖s / (s - 1) - s * abelZetaRemainder s‖ ≤
        ‖s / (s - 1)‖ + ‖s * abelZetaRemainder s‖ := norm_sub_le _ _
    _ = ‖s‖ / ‖s - 1‖ + ‖s‖ * ‖abelZetaRemainder s‖ := by rw [norm_div, norm_mul]
    _ ≤ ‖s‖ + ‖s‖ * 4 := by
      gcongr
      exact div_le_self (norm_nonneg s) hDen
    _ = 5 * ‖s‖ := by ring

end MathCollab.Density.ZetaGrowth
