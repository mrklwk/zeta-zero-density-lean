module
public import MathCollab.Density.GammaStrip
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Tactic

@[expose] public section

open Set MeasureTheory
open scoped Topology

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- Uniform on the entire detector strip, including zero ordinate. -/
theorem norm_Gamma_detector_strip {a t : ℝ} (ha : -(1/2 : ℝ) ≤ a) (ha' : a ≤ -(1/4 : ℝ)) :
    ‖Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)‖ ≤
      48*(1+|t|)*Real.exp (-|t|) := by
  let z : ℂ := (a : ℂ)+(t : ℂ)*Complex.I
  have hz : z ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp [z] at hr
    linarith
  have hlower : (1/4 : ℝ) ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    have hre : z.re = a := by simp [z]
    rw [hre, abs_of_neg (show a < 0 by linarith)] at h
    linarith
  have hrec := congrArg norm (Complex.Gamma_add_one z hz)
  rw [norm_mul] at hrec
  have hshift := GammaBounds.norm_Gamma_positive_strip_le_exp
    (s := a+1) (t := t) (by linarith) (by linarith)
  have he : z+1 = GammaBounds.stripPoint (a+1) t := by
    dsimp [z, GammaBounds.stripPoint]
    push_cast
    ring
  rw [← he, hrec] at hshift
  change ‖Complex.Gamma z‖ ≤ _
  nlinarith [norm_nonneg (Complex.Gamma z)]

theorem continuous_Gamma_detector_strip {a : ℝ} (ha : -(1/2 : ℝ) ≤ a)
    (ha' : a ≤ -(1/4 : ℝ)) :
    Continuous (fun t : ℝ => Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (Complex.continuousAt_Gamma _ ?_).comp (by fun_prop)
  intro m he
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
    Complex.neg_re, Complex.natCast_re] at hre
  by_cases hm : m = 0
  · subst m
    norm_num at hre
    linarith
  · have hm' : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    linarith

/-- Exponential decay on the whole horizontal contour strip up to the initial line 2. -/
theorem norm_Gamma_contour_strip {a t : ℝ} (ha : -(1/2 : ℝ) ≤ a) (ha' : a ≤ 2)
    (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)‖ ≤
      12*(1+|t|)^2*Real.exp (-|t|) := by
  have hbase : 0 ≤ 12*(1+|t|)*Real.exp (-|t|) := by positivity
  have hup : 12*(1+|t|)*Real.exp (-|t|) ≤
      12*(1+|t|)^2*Real.exp (-|t|) := by
    nlinarith [mul_nonneg hbase (abs_nonneg t)]
  by_cases hlow : a ≤ 1/2
  · have h : ‖Complex.Gamma ((a : ℂ)+(t : ℂ)*Complex.I)‖ ≤
        12*(1+|t|)*Real.exp (-|t|) := by
      simpa [GammaBounds.stripPoint] using GammaBounds.norm_Gamma_compactStrip_le_exp ha hlow ht
    exact h.trans hup
  · by_cases hmid : a ≤ 3/2
    · exact (GammaBounds.norm_Gamma_positive_strip_le_exp (by linarith) hmid).trans hup
    · let z : ℂ := ((a-1 : ℝ) : ℂ)+(t : ℂ)*Complex.I
      have hz : z ≠ 0 := by
        intro he
        have hr := congrArg Complex.re he
        simp [z] at hr
        linarith
      have he : (a : ℂ)+(t : ℂ)*Complex.I = z+1 := by
        dsimp [z]
        push_cast
        ring
      have hn : ‖z‖ ≤ 1+|t| := by
        have h := Complex.norm_le_abs_re_add_abs_im z
        have hp : 0 < a-1 := by linarith
        simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero,
          sub_self, add_zero, Complex.add_im, Complex.mul_im, mul_one,
          zero_add, abs_of_pos hp] at h
        linarith
      have hg := GammaBounds.norm_Gamma_positive_strip_le_exp
        (s := a-1) (t := t) (by linarith) (by linarith)
      rw [he, Complex.Gamma_add_one z hz, norm_mul]
      calc
        _ ≤ (1+|t|)*(12*(1+|t|)*Real.exp (-|t|)) :=
          mul_le_mul hn hg (norm_nonneg _) (by positivity)
        _ = _ := by ring

/-- Uniform gamma factor at the crossed zeta pole. -/
theorem norm_Gamma_one_sub_zero_le {ρ : ℂ} (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hγ : 1 ≤ |ρ.im|) :
    ‖Complex.Gamma (1-ρ)‖ ≤ 12*(1+|ρ.im|)*Real.exp (-|ρ.im|) := by
  have he : 1-ρ = ((1-ρ.re : ℝ) : ℂ)+((-ρ.im : ℝ) : ℂ)*Complex.I := by
    apply Complex.ext <;> simp
  rw [he]
  simpa [GammaBounds.stripPoint] using GammaBounds.norm_Gamma_compactStrip_le_exp
    (a := 1-ρ.re) (t := -ρ.im) (by linarith) (by linarith) (by simpa using hγ)

/-- An explicit integrable majorant independent of the zero and its real part. -/
def detectorGammaMajorant (t : ℝ) : ℝ := 48*(1+|t|)^2*Real.exp (-|t|)

theorem integrable_detectorGammaMajorant : Integrable detectorGammaMajorant := by
  have h0 := Real.GammaIntegral_convergent (s := 1) (by norm_num)
  have h1 := Real.GammaIntegral_convergent (s := 2) (by norm_num)
  have h2 := Real.GammaIntegral_convergent (s := 3) (by norm_num)
  norm_num at h0 h1 h2
  have hp : IntegrableOn (fun t : ℝ => 48*(1+t)^2*Real.exp (-t)) (Ioi 0) := by
    apply (((h0.add (h1.const_mul 2)).add h2).const_mul 48).congr
    filter_upwards with t
    change 48*((Real.exp (-t)+2*(Real.exp (-t)*t))+Real.exp (-t)*t^2) = _
    ring
  have hpabs : IntegrableOn detectorGammaMajorant (Ioi 0) := by
    apply hp.congr_fun _ measurableSet_Ioi
    intro t ht
    simp [detectorGammaMajorant, abs_of_pos (show 0 < t from ht)]
  have hn : IntegrableOn (fun t : ℝ => 48*(1+(-t))^2*Real.exp (-(-t))) (Iic 0) := by
    have hci : IntegrableOn (fun t : ℝ => 48*(1+t)^2*Real.exp (-t)) (Ici (-(0 : ℝ))) := by
      simpa using ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hp)
    exact hci.comp_neg_Iic
  have hnabs : IntegrableOn detectorGammaMajorant (Iic 0) := by
    apply hn.congr_fun _ measurableSet_Iic
    intro t ht
    simp [detectorGammaMajorant, abs_of_nonpos (show t ≤ 0 from ht)]
  have h := hnabs.union hpabs
  simpa only [Iic_union_Ioi, integrableOn_univ] using h

/-- The mass constant is fixed before beta; no gamma estimate is a premise. -/
theorem uniform_detector_gamma_mass :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, 3/4 ≤ β → β ≤ 1 →
      Integrable (fun t : ℝ => Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)) ∧
      Integrable (fun t : ℝ => (1+|t|)*
        ‖Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖) ∧
      (∫ t : ℝ, (1+|t|)*
        ‖Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)‖) ≤ C := by
  have hnonneg : 0 ≤ ∫ t : ℝ, detectorGammaMajorant t :=
    integral_nonneg (fun t => by dsimp [detectorGammaMajorant]; positivity)
  refine ⟨(∫ t : ℝ, detectorGammaMajorant t)+1, by linarith, ?_⟩
  intro β hβ hβ'
  let g := fun t : ℝ => Complex.Gamma (((1/2-β : ℝ) : ℂ)+(t : ℂ)*Complex.I)
  have hg : Continuous g := continuous_Gamma_detector_strip (by linarith) (by linarith)
  have hbound : ∀ t : ℝ, (1+|t|)*‖g t‖ ≤ detectorGammaMajorant t := by
    intro t
    have h := norm_Gamma_detector_strip (a := 1/2-β) (t := t) (by linarith) (by linarith)
    have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 1+|t| by positivity)
    dsimp [detectorGammaMajorant, g]
    nlinarith
  have hwcont : Continuous (fun t : ℝ => (1+|t|)*‖g t‖) := by fun_prop
  have hw : Integrable (fun t : ℝ => (1+|t|)*‖g t‖) :=
    integrable_detectorGammaMajorant.mono' hwcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact hbound t)
  have hgint : Integrable g := hw.mono' hg.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by nlinarith [abs_nonneg t, norm_nonneg (g t)])
  refine ⟨hgint, hw, ?_⟩
  exact (integral_mono hw integrable_detectorGammaMajorant hbound).trans (by linarith)

end MathCollab.Density
