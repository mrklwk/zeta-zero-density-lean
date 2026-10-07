module
public import MathCollab.Density.FixedBandError
public import MathCollab.Density.AllFrequency
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff ComplexConjugate

noncomputable section
namespace MathCollab.Density

def mellinLine (w : ℝ → ℂ) (r : ℝ) : ℂ := mellin w ((1 : ℂ) + r * I)

def oscillatoryKernel (v r z : ℝ) : ℂ :=
  (z : ℂ)⁻¹ * Complex.exp (I * (((v-r)*Real.log z - 2*Real.pi*z : ℝ) : ℂ))

theorem norm_dirichletPhase (x v : ℝ) : ‖dirichletPhase x v‖ = 1 := by
  simp [dirichletPhase, Complex.norm_exp]

theorem norm_oscillatoryKernel (v r z : ℝ) : ‖oscillatoryKernel v r z‖ = |z|⁻¹ := by
  simp [oscillatoryKernel, Complex.norm_exp]

theorem mellin_cpow_eq {x : ℝ} (hx : 0 < x) (r : ℝ) :
    (x : ℂ) ^ (-((1 : ℂ) + r * I)) = (x : ℂ)⁻¹ * dirichletPhase x (-r) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  have he : (Real.log x : ℂ) * (-(1 + (r : ℂ) * I)) =
      -(Real.log x : ℂ) + I * (((-r)*Real.log x : ℝ) : ℂ) := by push_cast; ring
  rw [he, Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hx]
  rfl

theorem cutoff_mellin_inversion_phase {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1/2 : ℝ) 5) {x : ℝ} (hx : 0 < x) :
    w x = ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ r : ℝ,
      (x : ℂ)⁻¹ * dirichletPhase x (-r) * mellinLine w r := by
  simpa only [mellin_cpow_eq hx, mellinLine] using cutoff_mellin_inversion hw hws hx

/-- The Jacobian and the real part one of Mellin inversion cancel exactly. -/
theorem scaled_mellin_phase {k z : ℝ} (hk : 0 < k) (hz : 0 < z) (v r : ℝ) :
    (k : ℂ)⁻¹ * (((z/k : ℝ) : ℂ)⁻¹ * dirichletPhase (z/k) (-r)) *
        Complex.exp (I * ((v * Real.log (z/k) - 2*Real.pi*z : ℝ) : ℂ)) =
      dirichletPhase k (r-v) * oscillatoryKernel v r z := by
  unfold dirichletPhase oscillatoryKernel
  have he : I * (((-r) * Real.log (z/k) : ℝ) : ℂ) +
      I * ((v * Real.log (z/k) - 2*Real.pi*z : ℝ) : ℂ) =
      I * (((r-v)*Real.log k : ℝ) : ℂ) +
      I * (((v-r)*Real.log z - 2*Real.pi*z : ℝ) : ℂ) := by
    rw [Real.log_div hz.ne' hk.ne']
    push_cast
    ring
  simp only [mul_assoc] at he ⊢
  rw [← Complex.exp_add, he, Complex.exp_add]
  push_cast
  field_simp [show (k : ℂ) ≠ 0 by exact_mod_cast hk.ne']

/-- Absolute product domination, with the full Mellin line retained. -/
theorem integrable_mellin_kernel {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1/2 : ℝ) 5) {a b : ℝ} (ha : 0 < a)
    (k v : ℝ) :
    Integrable (fun p : ℝ × ℝ => mellinLine w p.2 *
      (dirichletPhase k (p.2-v) * oscillatoryKernel v p.2 p.1))
      ((volume.restrict (Ioc a b)).prod volume) := by
  have hi : Integrable (fun z : ℝ => |z|⁻¹) (volume.restrict (Ioc a b)) := by
    have hh : IntegrableOn (fun z : ℝ => |z|⁻¹) (Icc a b) :=
      (continuousOn_id.abs.inv₀
        (fun z hz => abs_ne_zero.mpr (ha.trans_le hz.1).ne')).integrableOn_Icc
    exact hh.mono_set Ioc_subset_Icc_self
  have hm : Integrable (mellinLine w) := integrable_mellin_line_one hw hws
  have hp : Measurable (fun p : ℝ × ℝ =>
      dirichletPhase k (p.2-v) * oscillatoryKernel v p.2 p.1) := by
    unfold dirichletPhase oscillatoryKernel
    fun_prop
  apply (hi.mul_prod hm.norm).mono'
    (hm.aestronglyMeasurable.comp_snd.mul hp.aestronglyMeasurable)
  filter_upwards with p
  simp only [Pi.mul_apply, norm_mul, norm_dirichletPhase, norm_oscillatoryKernel, one_mul]
  exact le_of_eq (mul_comm _ _)

theorem integrable_mellin_kernel_slice {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1/2 : ℝ) 5) (k v z : ℝ) :
    Integrable (fun r : ℝ => mellinLine w r *
      (dirichletPhase k (r-v) * oscillatoryKernel v r z)) := by
  have hm : Integrable (mellinLine w) := integrable_mellin_line_one hw hws
  apply hm.mul_bdd (c := |z|⁻¹)
  · apply Measurable.aestronglyMeasurable
    unfold dirichletPhase oscillatoryKernel
    fun_prop
  · filter_upwards with r
    simp only [norm_mul, norm_dirichletPhase, norm_oscillatoryKernel, one_mul, le_refl]

/-- Fubini is justified by the proved product majorant, not assumed. -/
theorem mellin_kernel_integral_swap {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1/2 : ℝ) 5) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (k v : ℝ) :
    (∫ z in a..b, ∫ r : ℝ, mellinLine w r *
      (dirichletPhase k (r-v) * oscillatoryKernel v r z)) =
    ∫ r : ℝ, mellinLine w r * dirichletPhase k (r-v) *
      (∫ z in a..b, oscillatoryKernel v r z) := by
  rw [intervalIntegral_integral_swap (by
    simpa only [uIoc_of_le hab, Function.uncurry_def] using
      integrable_mellin_kernel hw hws (b := b) ha k v)]
  apply integral_congr_ae
  filter_upwards with r
  simp only [← mul_assoc, intervalIntegral.integral_const_mul]

/-- Positive dilation into any interval containing the scaled cutoff support. -/
theorem modeIntegral_scaled {w : ℝ → ℂ}
    (hws : tsupport w ⊆ Icc (1/2 : ℝ) 5) {k a b : ℝ}
    (hk : 0 < k) (hab : a ≤ b) (ha : a ≤ k / 2) (hb : 5*k ≤ b) (v : ℝ) :
    modeIntegral w v k = ∫ z in a..b, (k : ℂ)⁻¹ * w (z/k) *
      Complex.exp (I * ((v * Real.log (z/k) - 2*Real.pi*z : ℝ) : ℂ)) := by
  let f : ℝ → ℂ := fun y => w y *
    Complex.exp (I * ((v * Real.log y - 2*Real.pi*k*y : ℝ) : ℂ))
  have hg : modeIntegral w v k = ∫ y, f y := by
    unfold modeIntegral
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      have hn : y ∉ tsupport w := by
        intro hh
        apply hy
        change 0 < y
        linarith [(hws hh).1]
      simp only [image_eq_zero_of_notMem_tsupport hn, zero_mul])]
    apply integral_congr_ae
    filter_upwards with y
    dsimp [f]
    rw [mul_comm I]
  have hc : (∫ z, f (z/k)) = (k : ℂ) * ∫ y, f y := by
    simpa only [abs_of_pos hk, smul_eq_mul, Complex.real_smul] using
      Measure.integral_comp_div f k
  have hs : Function.support (fun z => f (z/k)) ⊆ Icc a b := by
    intro z hz
    have hwz : z/k ∈ tsupport w := by
      apply subset_tsupport w
      intro hzero
      exact hz (by simp [f, hzero])
    have hh := hws hwz
    have hzlo := (le_div_iff₀ hk).1 hh.1
    have hzhi := (div_le_iff₀ hk).1 hh.2
    constructor <;> nlinarith
  have hr : (∫ z in a..b, f (z/k)) = ∫ z, f (z/k) := by
    rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by by_contra hh; exact hz (hs hh))
  calc
    modeIntegral w v k = (k : ℂ)⁻¹ * ∫ z, f (z/k) := by
      rw [hg, hc]
      field_simp [show (k : ℂ) ≠ 0 by exact_mod_cast hk.ne']
    _ = (k : ℂ)⁻¹ * ∫ z in a..b, f (z/k) := by rw [hr]
    _ = ∫ z in a..b, (k : ℂ)⁻¹ * w (z/k) *
        Complex.exp (I * ((v * Real.log (z/k) - 2*Real.pi*z : ℝ) : ℂ)) := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro z _
      dsimp [f]
      have hh : 2*Real.pi*k*(z/k) = 2*Real.pi*z := by field_simp
      rw [hh]
      ring

/-- Pointwise Mellin expansion after the dilation, with no inverse-scale residue. -/
theorem scaled_cutoff_mellin {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1/2 : ℝ) 5) {k z : ℝ} (hk : 0 < k) (hz : 0 < z)
    (v : ℝ) :
    (k : ℂ)⁻¹ * w (z/k) *
        Complex.exp (I * ((v * Real.log (z/k) - 2*Real.pi*z : ℝ) : ℂ)) =
      ((1/(2*Real.pi) : ℝ) : ℂ) * ∫ r : ℝ,
        mellinLine w r * (dirichletPhase k (r-v) * oscillatoryKernel v r z) := by
  rw [cutoff_mellin_inversion_phase hw hws (div_pos hz hk)]
  let C : ℂ := ((1/(2*Real.pi) : ℝ) : ℂ)
  let E : ℂ := Complex.exp (I * ((v * Real.log (z/k) - 2*Real.pi*z : ℝ) : ℂ))
  change (k : ℂ)⁻¹ * (C * ∫ r : ℝ,
      ((z/k : ℝ) : ℂ)⁻¹ * dirichletPhase (z/k) (-r) * mellinLine w r) * E = _
  calc
    _ = C * (∫ r : ℝ, (k : ℂ)⁻¹ *
        ((((z/k : ℝ) : ℂ)⁻¹ * dirichletPhase (z/k) (-r)) * mellinLine w r) * E) := by
      rw [integral_mul_const, integral_const_mul]
      ring
    _ = C * ∫ r : ℝ, mellinLine w r *
        (dirichletPhase k (r-v) * oscillatoryKernel v r z) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with r
      calc
        _ = mellinLine w r * ((k : ℂ)⁻¹ *
            (((z/k : ℝ) : ℂ)⁻¹ * dirichletPhase (z/k) (-r)) * E) := by ring
        _ = _ := by rw [show E = _ from rfl, scaled_mellin_phase hk hz]

/-- Exact common-interval Mellin identity, justified by absolute Fubini. -/
theorem modeIntegral_mellin_common {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1/2 : ℝ) 5) {k a b : ℝ}
    (hk : 0 < k) (ha : 0 < a) (hab : a ≤ b) (hlo : a ≤ k/2) (hhi : 5*k ≤ b)
    (v : ℝ) :
    modeIntegral w v k = ((1/(2*Real.pi) : ℝ) : ℂ) * ∫ r : ℝ,
      mellinLine w r * dirichletPhase k (r-v) *
        (∫ z in a..b, oscillatoryKernel v r z) := by
  rw [modeIntegral_scaled hws hk hab hlo hhi]
  calc
    _ = ∫ z in a..b, ((1/(2*Real.pi) : ℝ) : ℂ) * ∫ r : ℝ,
        mellinLine w r * (dirichletPhase k (r-v) * oscillatoryKernel v r z) := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le hab] at hz
      exact scaled_cutoff_mellin hw hws hk (ha.trans_le hz.1) v
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, mellin_kernel_integral_swap hw hws ha hab]

def reflectionKernel (H v r : ℝ) : ℂ :=
  ∫ z in H/(40*Real.pi)..(20*H/Real.pi), oscillatoryKernel v r z

theorem reflection_interval_pos {H : ℝ} (hH : 0 < H) : 0 < H/(40*Real.pi) := by
  positivity

theorem reflection_interval_order {H : ℝ} (hH : 0 < H) :
    H/(40*Real.pi) ≤ 20*H/Real.pi := by
  apply (div_le_div_iff₀ (by positivity) Real.pi_pos).2
  nlinarith [Real.pi_pos]

theorem band_modeIntegral_mellin {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1/2 : ℝ) 5) {L H : ℝ}
    (hL : 0 < L) (hH : 0 < H) {m : ℤ} (hm : inReflectionBand L H m) (v : ℝ) :
    modeIntegral w v ((m : ℝ)*L) = ((1/(2*Real.pi) : ℝ) : ℂ) * ∫ r : ℝ,
      mellinLine w r * dirichletPhase ((m : ℝ)*L) (r-v) * reflectionKernel H v r := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm.1
  apply modeIntegral_mellin_common hw hws (mul_pos hmpos hL)
    (reflection_interval_pos hH) (reflection_interval_order hH)
  · have hh := (div_le_iff₀ (by positivity : 0 < 20*Real.pi*L)).1 hm.2.1
    apply (div_le_iff₀ (by positivity : 0 < 40*Real.pi)).2
    nlinarith
  · have hh := (le_div_iff₀ (by positivity : 0 < Real.pi*L)).1 hm.2.2
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith

theorem integrable_reflection_kernel {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1/2 : ℝ) 5) {H : ℝ} (hH : 0 < H) (k v : ℝ) :
    Integrable (fun r => mellinLine w r * dirichletPhase k (r-v) * reflectionKernel H v r) := by
  have hh := (integrable_mellin_kernel hw hws
    (b := 20*H/Real.pi) (reflection_interval_pos hH) k v).integral_prod_right
  convert hh using 1
  funext r
  simp only [reflectionKernel, intervalIntegral.integral_of_le (reflection_interval_order hH),
    ← mul_assoc, integral_const_mul]

theorem norm_reflectionKernel_sq_le {H : ℝ} (hH : 0 < H) (v r : ℝ) :
    ‖reflectionKernel H v r‖ ^ 2 ≤ 2000 / H := by
  have hh := norm_oscillatoryIntegral_le (tau := v-r)
    (reflection_interval_pos hH) (reflection_interval_order hH)
  change ‖reflectionKernel H v r‖ ≤ 6 / Real.sqrt (2*Real.pi*(H/(40*Real.pi))) at hh
  have he : 2*Real.pi*(H/(40*Real.pi)) = H/20 := by field_simp; ring
  rw [he] at hh
  have hs : 0 < Real.sqrt (H/20) := Real.sqrt_pos.2 (by positivity)
  have hs2 := Real.sq_sqrt (show 0 ≤ H/20 by positivity)
  have hb := (le_div_iff₀ hs).1 hh
  have hb2 := mul_self_le_mul_self (mul_nonneg (norm_nonneg _) hs.le) hb
  have hn : 0 ≤ ‖reflectionKernel H v r‖ := norm_nonneg _
  apply (le_div_iff₀ hH).2
  nlinarith [sq_nonneg ‖reflectionKernel H v r‖]

theorem measurable_reflectionKernel {H : ℝ} (hH : 0 < H) (v : ℝ) :
    Measurable (reflectionKernel H v) := by
  have hm : Measurable (fun p : ℝ × ℝ => oscillatoryKernel v p.1 p.2) := by
    unfold oscillatoryKernel
    fun_prop
  have hh := hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (H/(40*Real.pi)) (20*H/Real.pi)))
  unfold reflectionKernel
  simpa only [intervalIntegral.integral_of_le (reflection_interval_order hH)]
    using hh.measurable

/-- The line-one Mellin transform is exactly the specified positive-axis cutoff integral. -/
theorem mellinLine_eq_cutoffIntegral (w : ReflectionCutoff) (r : ℝ) :
    mellinLine (fun x => (w x : ℂ)) r = cutoffIntegral w r := by
  unfold mellinLine mellin cutoffIntegral
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [add_sub_cancel_left, smul_eq_mul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (ne_of_gt hx)), ← Complex.ofReal_log hx.le]
  unfold dirichletPhase
  have he : (Real.log x : ℂ) * ((r : ℂ)*I) = I * ((r*Real.log x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he, mul_comm]

theorem dirichletPhase_eq_cpow {x : ℝ} (hx : 0 < x) (v : ℝ) :
    dirichletPhase x v = (x : ℂ) ^ (I * (v : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]
  unfold dirichletPhase
  congr 1
  push_cast
  ring

end MathCollab.Density
