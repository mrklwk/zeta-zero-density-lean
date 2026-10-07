module
public import MathCollab.Density.MellinKernel
public import Mathlib.Algebra.QuadraticDiscriminant

@[expose] public section

open MeasureTheory

noncomputable section
namespace MathCollab.Density

/-- Weighted Cauchy--Schwarz from the nonnegative quadratic integral. -/
theorem weighted_integral_sq_le {ρ f : ℝ → ℝ} (hρ : ∀ x, 0 ≤ ρ x)
    (hi : Integrable ρ) (hi₁ : Integrable (fun x => ρ x * f x))
    (hi₂ : Integrable (fun x => ρ x * f x ^ 2)) :
    (∫ x, ρ x * f x) ^ 2 ≤ (∫ x, ρ x) * ∫ x, ρ x * f x ^ 2 := by
  have hquad (c : ℝ) : 0 ≤ (∫ x, ρ x) * (c*c) +
      (-2 * ∫ x, ρ x * f x) * c + ∫ x, ρ x * f x ^ 2 := by
    have hn : 0 ≤ ∫ x, ρ x * (f x-c)^2 :=
      integral_nonneg (fun x => mul_nonneg (hρ x) (sq_nonneg _))
    have he : (∫ x, ρ x * (f x-c)^2) =
        (∫ x, ρ x * f x ^ 2) - 2*c*(∫ x, ρ x * f x) + c^2*(∫ x, ρ x) := by
      calc
        _ = ∫ x, (ρ x * f x ^ 2) - 2*c*(ρ x * f x) + c^2*ρ x := by
          apply integral_congr_ae
          filter_upwards with x
          ring
        _ = _ := by
          have hi₃ : Integrable (fun x => ρ x * f x ^ 2 - 2*c*(ρ x*f x)) :=
            hi₂.sub (hi₁.const_mul (2*c))
          rw [integral_add hi₃ (hi.const_mul (c^2)),
            integral_sub hi₂ (hi₁.const_mul (2*c)), integral_const_mul, integral_const_mul]
    rw [he] at hn
    nlinarith
  have hh := discrim_le_zero hquad
  unfold discrim at hh
  nlinarith

theorem integrable_weighted_norm_sq {W g : ℝ → ℂ} (hW : Integrable W)
    (hg : AEStronglyMeasurable g) {C : ℝ} (hb : ∀ x, ‖g x‖ ≤ C) :
    Integrable (fun x => ‖W x‖ * ‖g x‖ ^ 2) := by
  apply hW.norm.mul_bdd (hg.norm.pow 2) (c := C^2)
  filter_upwards with x
  simp only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖g x‖)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hb x) 2

/-- Complex weighted Cauchy--Schwarz with all integrability discharged by a bound. -/
theorem norm_integral_mul_sq_le {W g : ℝ → ℂ} (hW : Integrable W)
    (hg : AEStronglyMeasurable g) {C : ℝ} (hb : ∀ x, ‖g x‖ ≤ C) :
    ‖∫ x, W x * g x‖ ^ 2 ≤ (∫ x, ‖W x‖) * ∫ x, ‖W x‖ * ‖g x‖ ^ 2 := by
  have hi := hW.mul_bdd hg (Filter.Eventually.of_forall hb)
  have hi₁ : Integrable (fun x => ‖W x‖ * ‖g x‖) := by
    simpa only [norm_mul] using hi.norm
  have hh := weighted_integral_sq_le (fun x => norm_nonneg (W x)) hW.norm hi₁
    (integrable_weighted_norm_sq hW hg hb)
  have hn : ‖∫ x, W x * g x‖ ≤ ∫ x, ‖W x‖ * ‖g x‖ := by
    simpa only [norm_mul] using norm_integral_le_integral_norm (fun x => W x * g x)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hh

end MathCollab.Density
