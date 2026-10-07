module
public import MathCollab.Density.LargeValueDefinitions
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

@[expose] public section

open Real Complex Set MeasureTheory
open scoped ContDiff FourierTransform SchwartzMap

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- The stronger fixed cutoff required only for the comparison step. -/
structure ComparisonCutoff extends ReflectionCutoff where
  nonneg : ∀ x, 0 ≤ toFun x
  one_on : ∀ x ∈ Icc (1 : ℝ) 4, toFun x = 1

instance : CoeFun ComparisonCutoff (fun _ => ℝ → ℝ) := ⟨fun w => w.toFun⟩

def comparisonCutoff : ComparisonCutoff := by
  let f : ContDiffBump (5/2 : ℝ) :=
    { rIn := 3/2, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  refine
    { toFun := f
      smooth := f.contDiff
      support := ?_
      nonneg := ?_
      one_on := ?_ }
  · rw [f.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq] at hx
    have hh := abs_le.mp hx
    dsimp [f] at hh
    constructor <;> linarith
  · intro x
    exact f.nonneg
  · intro x hx
    apply f.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    change |x - 5/2| ≤ 3/2
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- Uniform quadratic decay of the continuous cutoff term, internalized from Mellin decay. -/
theorem cutoffIntegral_quadratic_decay (w : ReflectionCutoff) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ, ‖cutoffIntegral w v‖ ≤ C/(1+|v|)^2 := by
  let f : ℝ → ℂ := fun x => (w x : ℂ)
  have hs : ∀ x, x ∉ Icc (1/2 : ℝ) 5 → f x = 0 :=
    fun x hx => image_eq_zero_of_notMem_tsupport (fun hh => hx (w.complex_support hh))
  let ψ := Transforms.mellinLogLiftSchwartz f
    (Transforms.mellinLogLift_hasCompactSupport (by norm_num) (by norm_num) hs)
    (Transforms.mellinLogLift_contDiff w.complex_smooth)
  let C₀ : ℝ := SchwartzMap.seminorm ℂ 0 0 (𝓕 ψ)
  let C₂ : ℝ := SchwartzMap.seminorm ℂ 2 0 (𝓕 ψ)
  have hC₀ : 0 ≤ C₀ := apply_nonneg _ _
  have hC₂ : 0 ≤ C₂ := apply_nonneg _ _
  refine ⟨2*C₀ + 2*(2*Real.pi)^2*C₂, by positivity, ?_⟩
  intro v
  have h₀ := Transforms.scaledPower_mul_norm_mellin_line_one_le_seminorm
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 5) hs w.complex_smooth 0 v
  have h₂ := Transforms.scaledPower_mul_norm_mellin_line_one_le_seminorm
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (0 : ℝ) < 5) hs w.complex_smooth 2 v
  change |v/(2*Real.pi)|^0 * ‖mellinLine f v‖ ≤ C₀ at h₀
  change |v/(2*Real.pi)|^2 * ‖mellinLine f v‖ ≤ C₂ at h₂
  rw [mellinLine_eq_cutoffIntegral] at h₀ h₂
  simp only [pow_zero, one_mul] at h₀
  have h₂' : v^2 * ‖cutoffIntegral w v‖ ≤ (2*Real.pi)^2*C₂ := by
    have hh := mul_le_mul_of_nonneg_left h₂ (sq_nonneg (2*Real.pi))
    have he : (2*Real.pi)^2 * (|v/(2*Real.pi)|^2 * ‖cutoffIntegral w v‖) =
        v^2 * ‖cutoffIntegral w v‖ := by rw [sq_abs, div_pow]; field_simp
    rw [he] at hh
    exact hh
  have hv : (1+|v|)^2 ≤ 2+2*v^2 := by nlinarith [sq_abs v, sq_nonneg (|v|-1)]
  have hh := mul_le_mul_of_nonneg_right hv (norm_nonneg (cutoffIntegral w v))
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (1+|v|)^2)).2
  nlinarith

end MathCollab.Density
