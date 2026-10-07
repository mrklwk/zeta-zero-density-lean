module
/-
The termwise Mellin proof is adapted from McColm TypeIICoverage at
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, MIT. The cutoff X and smoothing
variable x are independent real parameters. No upstream project imports.
-/
public import MathCollab.Density.MollifierDirichlet
public import MathCollab.Density.GammaMellin
public import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped ArithmeticFunction.Moebius BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

theorem integrable_tsum_of_summable_integral_norm
    {α : Type*} [MeasurableSpace α] {measure : Measure α}
    {F : ℕ → α → ℂ}
    (hFint : ∀ n, MeasureTheory.Integrable (F n) measure)
    (hFsum : Summable (fun n => ∫ x, ‖F n x‖ ∂measure)) :
    MeasureTheory.Integrable (fun x => ∑' n, F n x) measure := by
  have hMeas (n : ℕ) : AEStronglyMeasurable (F n) measure := (hFint n).1
  have hNormMeas (n : ℕ) : AEMeasurable (fun x => ‖F n x‖ₑ) measure :=
    (hMeas n).enorm
  have hLIntegral : ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂measure ≠ ⊤ := by
    have hEach (n : ℕ) : ∫⁻ x, ‖F n x‖ₑ ∂measure = ‖∫ x, ‖F n x‖ ∂measure‖₊ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hFint n).norm, ENNReal.coe_nnreal_eq,
        coe_nnnorm, Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F n x))]
      simp only [coe_nnnorm]
    rw [funext hEach]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hFsum.abs
  have hPointwise : ∀ᵐ x ∂measure, Summable (fun n => (‖F n x‖₊ : ℝ)) := by
    rw [← lintegral_tsum hNormMeas] at hLIntegral
    refine (ae_lt_top' (AEMeasurable.tsum hNormMeas) hLIntegral).mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  have hBoundInt : Integrable (fun x => ∑' n, ‖F n x‖) measure := by
    refine ⟨AEStronglyMeasurable.tsum (fun n => (hFint n).norm.1), ?_⟩
    dsimp [HasFiniteIntegral]
    have hFinite : ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂measure < ⊤ := by
      rw [lintegral_tsum hNormMeas, lt_top_iff_ne_top]
      exact hLIntegral
    convert hFinite using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm, NNReal.nnnorm_eq]
    filter_upwards [hPointwise] with x hx
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx)
  refine hBoundInt.mono' (AEStronglyMeasurable.tsum hMeas) ?_
  filter_upwards [hPointwise] with x hx
  exact norm_tsum_le_tsum_norm hx

def smoothedDetector (ρ : ℂ) (X x : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term (mollifierDirichletCoeff X) ρ n *
    Complex.exp (-((n : ℝ) * x))

theorem norm_mollifier_LSeries_term_le_cutoff {ρ : ℂ} (X : ℝ) (n : ℕ)
    (hρ : 0 ≤ ρ.re) :
    ‖LSeries.term (mollifierDirichletCoeff X) ρ n‖ ≤
      (⌊X⌋₊ : ℝ) := by
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hnOneNat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnOneNat
    have hPow : 1 ≤ (n : ℝ) ^ ρ.re := Real.one_le_rpow hnOne hρ
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hPow)).2
      ((norm_mollifierDirichletCoeff_le_cutoff X n).trans
        (by nlinarith [show (0 : ℝ) ≤ ⌊X⌋₊ by positivity]))

/-- Absolute convergence of the smoothed detector at every positive smoothing
parameter, uniformly for `Re ρ ≥ 0`. -/
theorem summable_smoothedDetector {ρ : ℂ} {X x : ℝ}
    (hx : 0 < x) (hρ : 0 ≤ ρ.re) :
    Summable (fun n : ℕ =>
      LSeries.term (mollifierDirichletCoeff X) ρ n *
        Complex.exp (-((n : ℝ) * x))) := by
  have hGeom : Summable (fun n : ℕ => Real.exp (-(n : ℝ) * x)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.summable_exp_nat_mul_iff.mpr (show -x < 0 by linarith))
  apply Summable.of_norm
  refine (hGeom.mul_left (⌊X⌋₊ : ℝ)).of_nonneg_of_le
    (fun n => norm_nonneg _) ?_
  intro n
  rw [norm_mul, Complex.norm_exp]
  have hRe : (-(((n : ℝ) : ℂ) * (x : ℂ))).re = -((n : ℝ) * x) := by
    norm_num
  rw [hRe]
  have hExpEq : Real.exp (-((n : ℝ) * x)) = Real.exp (-(n : ℝ) * x) := by
    congr 1
    ring
  rw [← hExpEq]
  apply mul_le_mul_of_nonneg_right
    (norm_mollifier_LSeries_term_le_cutoff X n hρ)
  exact (Real.exp_pos (-((n : ℝ) * x))).le

theorem hasSum_smoothedDetector {ρ : ℂ} {X x : ℝ}
    (hx : 0 < x) (hρ : 0 ≤ ρ.re) :
    HasSum (fun n : ℕ =>
      LSeries.term (mollifierDirichletCoeff X) ρ n *
        Complex.exp (-((n : ℝ) * x)))
      (smoothedDetector ρ X x) := by
  exact (summable_smoothedDetector (X := X) hx hρ).hasSum

theorem norm_LSeries_term_div_rpow_eq_add (f : ℕ → ℂ) (ρ s : ℂ) (n : ℕ) :
    ‖LSeries.term f ρ n‖ / (n : ℝ) ^ s.re =
      ‖LSeries.term f (ρ + s) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn, ite_eq_right hn]
    rw [add_re, Real.rpow_add hnPos]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hnPos ρ.re),
      ne_of_gt (Real.rpow_pos_of_pos hnPos s.re)]

theorem Gamma_mul_term_div_cpow_eq_add (f : ℕ → ℂ) (ρ s : ℂ) (n : ℕ) :
    Complex.Gamma s * LSeries.term f ρ n / (n : ℝ) ^ s =
      Complex.Gamma s * LSeries.term f (ρ + s) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [Complex.ofReal_natCast, Complex.cpow_add _ _ hnC]
    field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)]

set_option maxHeartbeats 800000 in
/-- Mellin transformation of the smoothed detector on every line where the
underlying zeta--Möbius L-series converges absolutely. -/
theorem mellin_smoothedDetector_eq {ρ s : ℂ} {X : ℝ}
    (hρ : 0 ≤ ρ.re) (hs : 0 < s.re)
    (hAbs : 1 < (ρ + s).re) :
    mellin (smoothedDetector ρ X) s =
      Complex.Gamma s * LSeries (mollifierDirichletCoeff X)
        (ρ + s) := by
  let f : ℕ → ℂ := mollifierDirichletCoeff X
  have hLS : LSeriesSummable f (ρ + s) :=
    mollifierDirichletCoeff_LSeriesSummable X hAbs
  have hSumNorm : Summable (fun n : ℕ =>
      ‖LSeries.term f ρ n‖ / (n : ℝ) ^ s.re) := by
    have hNorm : Summable (fun n : ℕ => ‖LSeries.term f (ρ + s) n‖) :=
      summable_norm_iff.mpr hLS
    exact hNorm.congr (fun n => (norm_LSeries_term_div_rpow_eq_add f ρ s n).symm)
  have hMellin : HasSum (fun n : ℕ =>
      Complex.Gamma s * LSeries.term f ρ n / (n : ℝ) ^ s)
      (mellin (smoothedDetector ρ X) s) := by
    apply hasSum_mellin
    · intro n
      rcases eq_or_ne n 0 with rfl | hn
      · left
        simp
      · right
        exact_mod_cast Nat.pos_of_ne_zero hn
    · exact hs
    · intro x hx
      have hSeries := hasSum_smoothedDetector (X := X) hx hρ
      simpa [f, Complex.ofReal_exp] using hSeries
    · exact hSumNorm
  have hMellin' : HasSum (fun n : ℕ =>
      Complex.Gamma s * LSeries.term f (ρ + s) n)
      (mellin (smoothedDetector ρ X) s) :=
    hMellin.congr_fun (fun n => (Gamma_mul_term_div_cpow_eq_add f ρ s n).symm)
  have hProduct : HasSum (fun n : ℕ =>
      Complex.Gamma s * LSeries.term f (ρ + s) n)
      (Complex.Gamma s * LSeries f (ρ + s)) := by
    exact hLS.hasSum.mul_left (Complex.Gamma s)
  exact hMellin'.unique hProduct

/-- A fixed convergent p-series used to dominate all right-line detector
L-series uniformly in the ordinate. -/
def detectorPSeries : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ (-(6 / 5 : ℝ))

theorem summable_detectorPSeries :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(6 / 5 : ℝ))) := by
  exact Real.summable_nat_rpow.mpr (by norm_num)

theorem detectorPSeries_nonneg : 0 ≤ detectorPSeries := by
  exact tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

theorem norm_mollifier_LSeries_le_cutoff_pSeries {z : ℂ} {X : ℝ}
    (hz : 6 / 5 ≤ z.re) :
    ‖LSeries (mollifierDirichletCoeff X) z‖ ≤
      (⌊X⌋₊ : ℝ) * detectorPSeries := by
  let f : ℕ → ℂ := mollifierDirichletCoeff X
  have hAbs : 1 < z.re := by linarith
  have hLS : LSeriesSummable f z :=
    mollifierDirichletCoeff_LSeriesSummable X hAbs
  have hNorm : Summable (fun n : ℕ => ‖LSeries.term f z n‖) :=
    summable_norm_iff.mpr hLS
  have hTerm (n : ℕ) : ‖LSeries.term f z n‖ ≤
      (⌊X⌋₊ : ℝ) * (n : ℝ) ^ (-(6 / 5 : ℝ)) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hDen : (n : ℝ) ^ (6 / 5 : ℝ) ≤ (n : ℝ) ^ z.re :=
        Real.rpow_le_rpow_of_exponent_le hnOne hz
      rw [LSeries.norm_term_eq, ite_eq_right hn]
      rw [Real.rpow_neg hnPos.le]
      have hCoeff := norm_mollifierDirichletCoeff_le_cutoff X n
      have hLeft : ‖f n‖ / (n : ℝ) ^ z.re ≤
          (⌊X⌋₊ : ℝ) / (n : ℝ) ^ z.re := by
        exact div_le_div_of_nonneg_right hCoeff (Real.rpow_nonneg hnPos.le _)
      have hRight : (⌊X⌋₊ : ℝ) / (n : ℝ) ^ z.re ≤
          (⌊X⌋₊ : ℝ) / (n : ℝ) ^ (6 / 5 : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hnPos _)
          hDen
      exact hLeft.trans hRight
  calc
    ‖LSeries f z‖ ≤ ∑' n : ℕ, ‖LSeries.term f z n‖ :=
      norm_tsum_le_tsum_norm hNorm
    _ ≤ ∑' n : ℕ, (⌊X⌋₊ : ℝ) *
        (n : ℝ) ^ (-(6 / 5 : ℝ)) := by
      exact hNorm.tsum_le_tsum hTerm
        (summable_detectorPSeries.mul_left (⌊X⌋₊ : ℝ))
    _ = (⌊X⌋₊ : ℝ) * detectorPSeries := by
      rw [detectorPSeries, tsum_mul_left]

set_option maxHeartbeats 800000 in
/-- The Mellin transform of the smoothed detector is genuinely integrable on
the right line `Re s = 1/2`, uniformly for the zero-density range `Re ρ ≥ 3/4`. -/
theorem verticalIntegrable_mellin_smoothedDetector {ρ : ℂ} {X : ℝ}
    (hρ : 3 / 4 ≤ ρ.re) :
    VerticalIntegrable (mellin (smoothedDetector ρ X)) (1 / 2 : ℝ) := by
  let line : ℝ → ℂ := fun u => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I
  let g : ℝ → ℂ := fun u => Complex.Gamma (line u) *
    (riemannZeta (ρ + line u) *
      zetaMollifier X (ρ + line u))
  have hGammaCont : Continuous (fun u : ℝ => Complex.Gamma (line u)) := by
    apply continuous_iff_continuousAt.2
    intro u
    have hNoPole : ∀ m : ℕ, line u ≠ -m := by
      intro m hm
      have hRe := congrArg Complex.re hm
      have hmNonneg : (0 : ℝ) ≤ m := by positivity
      simp [line] at hRe
      linarith
    exact ContinuousAt.comp' (Complex.differentiableAt_Gamma _ hNoPole).continuousAt
      (by dsimp [line]; fun_prop)
  have hZetaCont : Continuous (fun u : ℝ => riemannZeta (ρ + line u)) := by
    apply continuous_iff_continuousAt.2
    intro u
    have hzRe : 1 < (ρ + line u).re := by simp [line]; linarith
    have hzNe : ρ + line u ≠ 1 := by
      intro hz
      have hRe := congrArg Complex.re hz
      simp [line] at hRe
      linarith
    exact ContinuousAt.comp' (differentiableAt_riemannZeta hzNe).continuousAt
      (by dsimp [line]; fun_prop)
  have hMollCont : Continuous (fun u : ℝ => zetaMollifier X (ρ + line u)) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact ContinuousAt.comp' (differentiableAt_zetaMollifier X (ρ + line u)).continuousAt (by
      dsimp [line]; fun_prop)
  have hgCont : Continuous g := by
    exact hGammaCont.mul (hZetaCont.mul hMollCont)
  let C : ℝ := (⌊X⌋₊ : ℝ) * detectorPSeries
  have hDom : MeasureTheory.Integrable (fun u : ℝ =>
      C * ‖Complex.Gamma (line u)‖) := by
    have hGammaInt : MeasureTheory.Integrable
        (fun u : ℝ => Complex.Gamma (line u)) := by
      simpa [line, VerticalIntegrable] using GammaMellin.verticalIntegrable_Gamma (sigma := 1/2) (by norm_num)
    exact hGammaInt.norm.const_mul C
  have hg : MeasureTheory.Integrable g := by
    refine MeasureTheory.Integrable.mono' hDom hgCont.aestronglyMeasurable ?_
    filter_upwards with u
    have hzRe : 6 / 5 ≤ (ρ + line u).re := by simp [line]; linarith
    have hAbs : 1 < (ρ + line u).re := by linarith
    have hLSeries := norm_mollifier_LSeries_le_cutoff_pSeries (X := X) hzRe
    have hProduct := riemannZeta_mul_zetaMollifier_eq_LSeries
      X hAbs
    dsimp [g]
    rw [norm_mul, hProduct]
    dsimp [C]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hLSeries
      (norm_nonneg (Complex.Gamma (line u)))
  apply hg.congr
  filter_upwards with u
  have hsRe : 0 < (line u).re := by simp [line]
  have hρNonneg : 0 ≤ ρ.re := by linarith
  have hAbs : 1 < (ρ + line u).re := by simp [line]; linarith
  rw [mellin_smoothedDetector_eq (X := X) hρNonneg hsRe hAbs]
  dsimp [g]
  rw [riemannZeta_mul_zetaMollifier_eq_LSeries
    X hAbs]

set_option maxHeartbeats 800000 in
/-- The smoothed detector is continuous at every positive smoothing
parameter.  Uniform convergence is obtained on the neighborhood `[x/2,∞)`
from the same geometric majorant used for absolute convergence. -/
theorem continuousAt_smoothedDetector {ρ : ℂ} {X x : ℝ}
    (hx : 0 < x) (hρ : 0 ≤ ρ.re) :
    ContinuousAt (smoothedDetector ρ X) x := by
  let x₀ : ℝ := x / 2
  let term : ℕ → ℝ → ℂ := fun n y =>
    LSeries.term (mollifierDirichletCoeff X) ρ n *
      Complex.exp (-((n : ℝ) * y))
  let majorant : ℕ → ℝ := fun n =>
    (⌊X⌋₊ : ℝ) * Real.exp (-((n : ℝ) * x₀))
  have hx₀ : 0 < x₀ := by dsimp [x₀]; linarith
  have hMajorant : Summable majorant := by
    have hGeom : Summable (fun n : ℕ => Real.exp (-(n : ℝ) * x₀)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.summable_exp_nat_mul_iff.mpr (show -x₀ < 0 by linarith))
    simpa [majorant] using hGeom.mul_left (⌊X⌋₊ : ℝ)
  have hTermCont (n : ℕ) : ContinuousOn (term n) (Set.Ici x₀) := by
    apply Continuous.continuousOn
    dsimp [term]
    fun_prop
  have hBound (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ici x₀) :
      ‖term n y‖ ≤ majorant n := by
    have hnNonneg : (0 : ℝ) ≤ n := by positivity
    have hArg : -((n : ℝ) * y) ≤ -((n : ℝ) * x₀) := by
      have := hy
      simp only [Set.mem_Ici] at this
      nlinarith
    have hExp : Real.exp (-((n : ℝ) * y)) ≤
        Real.exp (-((n : ℝ) * x₀)) := Real.exp_le_exp.mpr hArg
    dsimp [term, majorant]
    rw [norm_mul, Complex.norm_exp]
    have hRe : (-((n : ℂ) * (y : ℂ))).re = -((n : ℝ) * y) := by
      norm_num
    rw [hRe]
    calc
      ‖LSeries.term (mollifierDirichletCoeff X) ρ n‖ *
          Real.exp (-((n : ℝ) * y))
          ≤ (⌊X⌋₊ : ℝ) * Real.exp (-((n : ℝ) * y)) :=
        mul_le_mul_of_nonneg_right
          (norm_mollifier_LSeries_term_le_cutoff X n hρ)
          (Real.exp_pos _).le
      _ ≤ (⌊X⌋₊ : ℝ) * Real.exp (-((n : ℝ) * x₀)) :=
        mul_le_mul_of_nonneg_left hExp (by positivity)
  have hContinuousOn : ContinuousOn (smoothedDetector ρ X) (Set.Ici x₀) := by
    change ContinuousOn (fun y => ∑' n : ℕ, term n y) (Set.Ici x₀)
    exact continuousOn_tsum hTermCont hMajorant hBound
  have hNhd : Set.Ici x₀ ∈ nhds x := by
    apply Filter.mem_of_superset
      (Ioi_mem_nhds (show x₀ < x by dsimp [x₀]; linarith))
    exact Set.Ioi_subset_Ici_self
  exact hContinuousOn.continuousAt hNhd

set_option maxHeartbeats 800000 in
/-- Absolute convergence in the Mellin variable on `Re s = 1/2`.  The key
summability exponent is `Re ρ + 1/2 > 1`; this is exactly why the detector
works uniformly in the repaired zero-density range `Re ρ ≥ 3/4`. -/
theorem mellinConvergent_smoothedDetector {ρ : ℂ} {X : ℝ}
    (hρ : 3 / 4 ≤ ρ.re) :
    MellinConvergent (smoothedDetector ρ X) ((1 / 2 : ℝ) : ℂ) := by
  let f : ℕ → ℂ := mollifierDirichletCoeff X
  let s : ℂ := ((1 / 2 : ℝ) : ℂ)
  let a : ℕ → ℂ := fun n => LSeries.term f ρ n
  let term : ℕ → ℝ → ℂ := fun n t =>
    a n * ((t : ℂ) ^ (s - 1) * Real.exp (-(n : ℝ) * t))
  have hs : 0 < s.re := by simp [s]
  have hAbs : 1 < (ρ + s).re := by simp [s]; linarith
  have hLS : LSeriesSummable f (ρ + s) :=
    mollifierDirichletCoeff_LSeriesSummable X hAbs
  have hSumNorm : Summable (fun n => ‖a n‖ / (n : ℝ) ^ s.re) := by
    have hNorm : Summable (fun n => ‖LSeries.term f (ρ + s) n‖) :=
      summable_norm_iff.mpr hLS
    exact hNorm.congr fun n => by
      simpa [a] using (norm_LSeries_term_div_rpow_eq_add f ρ s n).symm
  have hTermInt (n : ℕ) : MeasureTheory.IntegrableOn (term n) (Set.Ioi 0) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [term, a, LSeries.term]
    · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hGamma := Complex.GammaIntegral_convergent hs
      rw [← mul_zero (n : ℝ),
        ← integrableOn_Ioi_comp_mul_left_iff _ _ hnPos] at hGamma
      refine (MeasureTheory.IntegrableOn.congr_fun
        (hGamma.const_mul (1 / (((n : ℝ) : ℂ) ^ (s - 1)))) ?_ measurableSet_Ioi).const_mul (a n)
      intro t ht
      change 1 / (((n : ℝ) : ℂ) ^ (s - 1)) *
          ((Real.exp (-((n : ℝ) * t)) : ℂ) *
            ((((n : ℝ) * t : ℝ) : ℂ) ^ (s - 1))) =
        (t : ℂ) ^ (s - 1) * (Real.exp (-(n : ℝ) * t) : ℂ)
      rw [mul_comm (Real.exp _ : ℂ), ← mul_assoc, neg_mul, Complex.ofReal_mul]
      rw [Complex.mul_cpow_ofReal_nonneg hnPos.le ht.le, ← mul_assoc, one_div,
        inv_mul_cancel₀, one_mul]
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Complex.ofReal_ne_zero.mpr hnPos.ne')
  have hTermSum : Summable (fun n => ∫ t in Set.Ioi 0, ‖term n t‖) := by
    apply Summable.of_norm
    convert! hSumNorm.mul_left (Real.Gamma s.re) using 2 with n
    simp_rw [term, norm_mul (a n), integral_const_mul]
    rw [← mul_div_assoc, mul_comm (Real.Gamma _), mul_div_assoc,
      norm_mul ‖a n‖, norm_norm]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [a, LSeries.term]
    congr 1
    have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hReal := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hnPos
    simp_rw [← neg_mul (n : ℝ), one_div, Real.inv_rpow hnPos.le,
      ← div_eq_inv_mul] at hReal
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← hReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  have hSeriesInt : MeasureTheory.IntegrableOn (fun t => ∑' n, term n t) (Set.Ioi 0) :=
    integrable_tsum_of_summable_integral_norm hTermInt hTermSum
  rw [MellinConvergent]
  apply hSeriesInt.congr_fun
  · intro t ht
    have htPos : 0 < t := ht
    have hSeries := hasSum_smoothedDetector (X := X) htPos (by linarith : 0 ≤ ρ.re)
    have hMul := hSeries.mul_left ((t : ℂ) ^ (s - 1))
    calc
      ∑' n, term n t = ∑' n,
          (t : ℂ) ^ (s - 1) *
            (LSeries.term (mollifierDirichletCoeff X) ρ n *
              Complex.exp (-((n : ℝ) * t))) := by
        apply tsum_congr
        intro n
        dsimp [term, a, f]
        rw [Complex.ofReal_exp]
        push_cast
        ring_nf
      _ = (t : ℂ) ^ (s - 1) * smoothedDetector ρ X t := by
        simpa [Complex.ofReal_exp] using hMul.tsum_eq
  · exact measurableSet_Ioi


/-- Exact inversion for an arbitrary positive smoothing variable. -/
theorem smoothedDetector_eq_mellinInv {ρ : ℂ} {X x : ℝ}
    (hx : 0 < x) (hρ : 3/4 ≤ ρ.re) :
    smoothedDetector ρ X x = mellinInv (1/2 : ℝ)
      (fun s => Complex.Gamma s * LSeries (mollifierDirichletCoeff X) (ρ+s)) x := by
  have hInv := mellinInv_mellin_eq (1/2 : ℝ) (smoothedDetector ρ X) hx
    (mellinConvergent_smoothedDetector hρ)
    (verticalIntegrable_mellin_smoothedDetector hρ)
    (continuousAt_smoothedDetector hx (by linarith : 0 ≤ ρ.re))
  rw [← hInv, mellinInv, mellinInv]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  rw [mellin_smoothedDetector_eq (by linarith : 0 ≤ ρ.re) (by norm_num)
    (by simp; linarith)]

/-- The literal Gamma-zeta-mollifier contour kernel, with independent X and Y. -/
def detectorKernel (ρ : ℂ) (X Y : ℝ) (s : ℂ) : ℂ :=
  (Y : ℂ)^s * Complex.Gamma s * zetaMollifier X (ρ+s) * riemannZeta (ρ+s)

/-- The positive smoothing scale produces the exact right contour, with no
zero or Weyl hypothesis. The factor is 1/(2*pi) for a real vertical parameter. -/
theorem smoothedDetector_eq_rightContour {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hρ : 3/4 ≤ ρ.re) :
    smoothedDetector ρ X (1/Y) =
      (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ u : ℝ,
        detectorKernel ρ X Y (((1/2 : ℝ) : ℂ)+(u : ℂ)*I)) := by
  rw [smoothedDetector_eq_mellinInv (one_div_pos.mpr hY) hρ,
    mellinInv, Complex.real_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards with u
  let s : ℂ := ((1/2 : ℝ) : ℂ)+(u : ℂ)*I
  have hAbs : 1 < (ρ+s).re := by simp [s]; linarith
  have hPow : ((1/Y : ℝ) : ℂ)^(-s) = (Y : ℂ)^s := by
    simpa using GammaMellin.cpow_neg_div_eq_reverse_cpow (x := 1) (by norm_num) hY s
  change ((1/Y : ℝ) : ℂ)^(-s) *
    (Complex.Gamma s * LSeries (mollifierDirichletCoeff X) (ρ+s)) = detectorKernel ρ X Y s
  rw [hPow, ← riemannZeta_mul_zetaMollifier_eq_LSeries X hAbs]
  unfold detectorKernel
  ring

end MathCollab.Density
