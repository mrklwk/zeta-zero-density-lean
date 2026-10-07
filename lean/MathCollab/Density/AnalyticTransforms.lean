module
/-
Selected proofs adapted from Conor Grogan's prime-minor-arcs-2-15,
commit f369f267b4dcfebf010c8e7baa2c9602e2960eba, Apache-2.0.
See ../../../third_party/grogan/README.md and LICENSE.
No upstream project module is imported.
-/
public import Mathlib.Analysis.MellinInversion
public import Mathlib.Analysis.Fourier.PoissonSummation
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

open Real Complex Set MeasureTheory
open scoped BigOperators FourierTransform SchwartzMap ContDiff

noncomputable section
namespace MathCollab.Density.Transforms

def sourcePhase (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * x : ℝ) * Complex.I)

theorem schwartz_poisson_at_zero (h : SchwartzMap ℝ ℂ) :
    ∑' n : ℤ, h n = ∑' n : ℤ, FourierTransform.fourier h n := by
  simpa using h.tsum_eq_tsum_fourier 0

theorem fourier_scaled_modulated
    (psi : ℝ → ℂ) {A : ℝ} (hA : 0 < A) (y w : ℝ) :
    FourierTransform.fourier
        (fun v : ℝ => psi (A * v) * sourcePhase (y * v)) w =
      (A⁻¹ : ℝ) • FourierTransform.fourier psi ((w - y) / A) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  have hpoint (v : ℝ) :
      Complex.exp ((-(2 * Real.pi * v * w) : ℝ) * Complex.I) •
          (psi (A * v) * sourcePhase (y * v)) =
        (fun t : ℝ =>
          Complex.exp ((-2 * Real.pi * t * ((w - y) / A) : ℝ) * Complex.I) •
            psi t) (A * v) := by
    simp only [sourcePhase, smul_eq_mul]
    calc
      Complex.exp ((-(2 * Real.pi * v * w) : ℝ) * Complex.I) *
          (psi (A * v) * Complex.exp ((2 * Real.pi * (y * v) : ℝ) * Complex.I)) =
          (Complex.exp ((-(2 * Real.pi * v * w) : ℝ) * Complex.I) *
            Complex.exp ((2 * Real.pi * (y * v) : ℝ) * Complex.I)) *
              psi (A * v) := by ring
      _ = Complex.exp ((-2 * Real.pi * (A * v) * ((w - y) / A) : ℝ) *
            Complex.I) * psi (A * v) := by
        rw [← Complex.exp_add]
        congr 2
        push_cast
        field_simp [ne_of_gt hA]
        ring
  calc
    (∫ v : ℝ, Complex.exp ((-2 * Real.pi * v * w : ℝ) * Complex.I) •
        (psi (A * v) * sourcePhase (y * v))) =
        ∫ v : ℝ, (fun t : ℝ =>
          Complex.exp ((-2 * Real.pi * t * ((w - y) / A) : ℝ) * Complex.I) •
            psi t) (A * v) := by
      apply integral_congr_ae
      filter_upwards with v
      convert hpoint v using 1
      ring_nf
    _ = (A⁻¹ : ℝ) • ∫ t : ℝ,
        Complex.exp ((-2 * Real.pi * t * ((w - y) / A) : ℝ) * Complex.I) •
          psi t := by
      simpa only [abs_of_pos (inv_pos.mpr hA)] using
        (Measure.integral_comp_mul_left
          (g := fun t : ℝ =>
            Complex.exp ((-2 * Real.pi * t * ((w - y) / A) : ℝ) * Complex.I) •
              psi t) A)

theorem scaled_modulated_poisson
    (psi : ℝ → ℂ) (hpsi_compact : HasCompactSupport psi)
    (hpsi_smooth : ContDiff ℝ ∞ psi) {A : ℝ} (hA : 0 < A) (y : ℝ) :
    ∑' ell : ℤ, psi (A * ell) * sourcePhase (y * ell) =
      (A⁻¹ : ℝ) • ∑' j : ℤ,
        FourierTransform.fourier psi ((j - y) / A) := by
  have hscaled_compact : HasCompactSupport (fun x : ℝ => psi (A * x)) := by
    let Au : ℝˣ := Units.mk0 A hA.ne'
    simpa only [Function.comp_apply, Units.smul_def, Au, Units.val_mk0] using!
      hpsi_compact.comp_homeomorph (Homeomorph.smul Au)
  have hcompact : HasCompactSupport
      (fun x : ℝ => psi (A * x) * sourcePhase (y * x)) := by
    simpa only [Pi.mul_apply] using! hscaled_compact.mul_right
  have hsmooth : ContDiff ℝ ∞
      (fun x : ℝ => psi (A * x) * sourcePhase (y * x)) := by
    apply ContDiff.mul
    · fun_prop
    · unfold sourcePhase
      apply Complex.contDiff_exp.comp
      apply ContDiff.mul
      · simpa only [Complex.ofRealCLM_apply] using!
          Complex.ofRealCLM.contDiff.comp
            (show ContDiff ℝ ∞ (fun x : ℝ => 2 * Real.pi * (y * x)) by fun_prop)
      · exact contDiff_const
  let h : SchwartzMap ℝ ℂ := hcompact.toSchwartzMap hsmooth
  calc
    ∑' ell : ℤ, psi (A * ell) * sourcePhase (y * ell) =
        ∑' ell : ℤ, h ell := by rfl
    _ = ∑' j : ℤ, FourierTransform.fourier h j := schwartz_poisson_at_zero h
    _ = ∑' j : ℤ, (A⁻¹ : ℝ) •
        FourierTransform.fourier psi ((j - y) / A) := by
      apply tsum_congr
      intro j
      simpa [h, HasCompactSupport.toSchwartzMap] using!
        fourier_scaled_modulated psi hA y j
    _ = (A⁻¹ : ℝ) • ∑' j : ℤ,
        FourierTransform.fourier psi ((j - y) / A) := by
      rw [tsum_const_smul'']

/-- A continuous compactly supported cutoff is Mellin-convergent on the
source line `Re(s)=1`.  This discharges the easy half of the analytic
hypotheses in `mellin_inversion_line_one`; only vertical decay of the Mellin
transform remains. -/
theorem mellinConvergent_one_of_compactSupport
    {f : ℝ → ℂ} (hf : Continuous f) (hcompact : HasCompactSupport f) :
    MellinConvergent f (1 : ℂ) := by
  unfold MellinConvergent
  have hi : IntegrableOn f (Set.Ioi 0) :=
    (hf.integrable_of_hasCompactSupport hcompact).integrableOn
  apply hi.congr_fun
  intro x hx
  simp
  exact measurableSet_Ioi

/-- Quadratic vertical decay is enough for the exact vertical-integrability
hypothesis of Mellin inversion.  The source obtains much faster decay by
repeated integration by parts; this theorem isolates the weakest concrete
decay estimate still needed for Lemma 6.2. -/
theorem verticalIntegrable_mellin_of_quadratic_decay
    {f : ℝ → ℂ} {C : ℝ}
    (hcontinuous : Continuous (fun r : ℝ =>
      mellin f ((1 : ℂ) + r * Complex.I)))
    (hdecay : ∀ r : ℝ,
      ‖mellin f ((1 : ℂ) + r * Complex.I)‖ ≤ C * (1 + r ^ 2)⁻¹) :
    Complex.VerticalIntegrable (mellin f) 1 := by
  unfold Complex.VerticalIntegrable
  have hmajor : Integrable (fun r : ℝ => C * (1 + r ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  exact hmajor.mono' hcontinuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hdecay)

/-- Mathlib's Mellin inversion theorem written on the literal source line
`Re(s)=1`, with `s=1+ir`. -/
theorem mellin_inversion_line_one
    (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x)
    (hconv : MellinConvergent f (1 : ℂ))
    (hvertical : Complex.VerticalIntegrable (mellin f) 1)
    (hcontinuous : ContinuousAt f x) :
    f x =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ r : ℝ,
          (x : ℂ) ^ (-((1 : ℂ) + r * Complex.I)) *
            mellin f ((1 : ℂ) + r * Complex.I) := by
  have h := mellinInv_mellin_eq 1 f hx hconv hvertical hcontinuous
  rw [mellinInv] at h
  simpa only [Complex.real_smul, Complex.ofReal_one, smul_eq_mul] using h.symm

def mellinLogLift (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) * f (Real.exp (-u))

theorem mellinLogLift_contDiff
    {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (mellinLogLift f) := by
  have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => -u) := contDiff_neg
  have hexpR : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Real.exp (-u)) :=
    Real.contDiff_exp.comp hneg
  have hexpC : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : ℝ => (Real.exp (-u) : ℂ)) := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using!
      Complex.ofRealCLM.contDiff.comp hexpR
  unfold mellinLogLift
  exact hexpC.mul (hf.comp hexpR)

theorem mellinLogLift_hasCompactSupport
    {a b : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0) :
    HasCompactSupport (mellinLogLift f) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (-Real.log b) (-Real.log a)))
  intro u hu
  unfold mellinLogLift
  have hexpNot : Real.exp (-u) ∉ Set.Icc a b := by
    intro hx
    apply hu
    constructor
    · have h := Real.exp_le_exp.mp
        (show Real.exp (-u) ≤ Real.exp (Real.log b) by
          simpa [Real.exp_log hb] using hx.2)
      linarith
    · have h := Real.exp_le_exp.mp
        (show Real.exp (Real.log a) ≤ Real.exp (-u) by
          simpa [Real.exp_log ha] using hx.1)
      linarith
  rw [hsupport _ hexpNot, mul_zero]

def mellinLogLiftSchwartz
    (f : ℝ → ℂ)
    (hcompact : HasCompactSupport (mellinLogLift f))
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) (mellinLogLift f)) :
    𝓢(ℝ, ℂ) :=
  hcompact.toSchwartzMap hsmooth

/-- Exact Mellin--Fourier conversion on `Re(s)=1`, including the `2π`
normalization. -/
theorem mellin_line_one_eq_fourier_logLift (f : ℝ → ℂ) (r : ℝ) :
    mellin f ((1 : ℂ) + r * Complex.I) =
      𝓕 (mellinLogLift f) (r / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hfun :
      (fun u : ℝ =>
        Real.exp (-((1 : ℂ) + r * Complex.I).re * u) •
          f (Real.exp (-u))) = mellinLogLift f := by
    funext u
    unfold mellinLogLift
    simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero,
      ofReal_im, I_im, zero_mul, sub_zero, neg_mul]
    rw [Complex.ofReal_exp]
    simp
  rw [hfun]
  simp

/-- Literal arbitrary-order Mellin decay.  For every natural `k`, the
scaled `k`th power times the Mellin transform is bounded by one explicit
Schwartz seminorm of the fixed cutoff. -/
theorem scaledPower_mul_norm_mellin_line_one_le_seminorm
    {a b : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (r : ℝ) :
    |r / (2 * Real.pi)| ^ k *
        ‖mellin f ((1 : ℂ) + r * Complex.I)‖ ≤
      SchwartzMap.seminorm ℂ k 0
        (𝓕 (mellinLogLiftSchwartz f
          (mellinLogLift_hasCompactSupport ha hb hsupport)
          (mellinLogLift_contDiff hf)) : 𝓢(ℝ, ℂ)) := by
  rw [mellin_line_one_eq_fourier_logLift]
  let psi : 𝓢(ℝ, ℂ) := mellinLogLiftSchwartz f
    (mellinLogLift_hasCompactSupport ha hb hsupport)
    (mellinLogLift_contDiff hf)
  have hFourier :
      𝓕 (mellinLogLift f) (r / (2 * Real.pi)) =
        ((𝓕 psi : 𝓢(ℝ, ℂ)) (r / (2 * Real.pi))) := by
    exact congrFun (SchwartzMap.fourier_coe psi).symm _
  rw [hFourier]
  have h := SchwartzMap.le_seminorm ℂ k 0
    (𝓕 psi) (r / (2 * Real.pi))
  simpa only [psi, mellinLogLiftSchwartz, norm_iteratedFDeriv_zero,
    Real.norm_eq_abs] using h

/-- Division form of arbitrary-order decay, valid away from `r=0`. -/
theorem norm_mellin_line_one_le_seminorm_div_scaledPower
    {a b : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) {r : ℝ} (hr : r ≠ 0) :
    ‖mellin f ((1 : ℂ) + r * Complex.I)‖ ≤
      SchwartzMap.seminorm ℂ k 0
        (𝓕 (mellinLogLiftSchwartz f
          (mellinLogLift_hasCompactSupport ha hb hsupport)
          (mellinLogLift_contDiff hf)) : 𝓢(ℝ, ℂ)) /
        |r / (2 * Real.pi)| ^ k := by
  apply (le_div_iff₀ (by positivity : 0 < |r / (2 * Real.pi)| ^ k)).2
  simpa [mul_comm] using
    (scaledPower_mul_norm_mellin_line_one_le_seminorm
      ha hb hsupport hf k r)


end MathCollab.Density.Transforms
