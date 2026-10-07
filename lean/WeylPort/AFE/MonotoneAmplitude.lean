module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.FirstDerivativeTest

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Decreasing amplitudes against a bounded oscillatory primitive

Integration by parts transfers an actual unweighted primitive bound to a
nonnegative decreasing C¹ amplitude. This avoids requiring monotonicity of
the combined amplitude/phase-derivative quotient.
-/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory

/-- A bounded primitive controls a nonnegative amplitude with nonpositive derivative. -/
theorem norm_integral_mul_le_of_primitive_bound {a b B : ℝ} (hab : a ≤ b)
    {g g' : ℝ → ℝ} {F f : ℝ → ℂ}
    (hg : ∀ x ∈ Set.Icc a b, HasDerivAt g (g' x) x)
    (hF : ∀ x ∈ Set.Icc a b, HasDerivAt F (f x) x)
    (hgc : ContinuousOn g' (Set.Icc a b)) (hfc : ContinuousOn f (Set.Icc a b))
    (hgpos : 0 ≤ g b) (hgneg : ∀ x ∈ Set.Icc a b, g' x ≤ 0)
    (hFa : F a = 0) (hB : ∀ x ∈ Set.Icc a b, ‖F x‖ ≤ B) :
    ‖∫ x in a..b, (g x : ℂ) * f x‖ ≤ g a * B := by
  have hi : IntervalIntegrable g' volume a b :=
    (Set.uIcc_of_le hab ▸ hgc).intervalIntegrable
  have hfi : IntervalIntegrable f volume a b :=
    (Set.uIcc_of_le hab ▸ hfc).intervalIntegrable
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => (hg x (Set.uIcc_of_le hab ▸ hx)).ofReal_comp)
    (fun x hx => hF x (Set.uIcc_of_le hab ▸ hx)) (Set.uIcc_of_le hab ▸ (Complex.continuous_ofReal.comp_continuousOn hgc)).intervalIntegrable hfi
  rw [hFa, mul_zero, sub_zero] at hparts
  have hnorm : ‖∫ x in a..b, (g' x : ℂ) * F x‖ ≤
      ∫ x in a..b, (-g' x) * B := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab
      (Filter.Eventually.of_forall (fun x hx => ?_)) (hi.neg.mul_const B)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (hgneg x ⟨hx.1.le, hx.2⟩)]
    exact mul_le_mul_of_nonneg_left (hB x ⟨hx.1.le, hx.2⟩)
      (neg_nonneg.mpr (hgneg x ⟨hx.1.le, hx.2⟩))
  have hderiv : (∫ x in a..b, g' x) = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hg x (Set.uIcc_of_le hab ▸ hx)) hi
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_neg, hderiv] at hnorm
  rw [hparts]
  calc
    _ ≤ ‖(g b : ℂ) * F b‖ + ‖∫ x in a..b, (g' x : ℂ) * F x‖ := norm_sub_le _ _
    _ ≤ g b * B + (-(g b - g a)) * B := by
      apply add_le_add _ hnorm
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgpos]
      exact mul_le_mul_of_nonneg_left (hB b (Set.right_mem_Icc.mpr hab)) hgpos
    _ = _ := by ring

end DhimanKadiriQuesadaHerrera2026
