module
/- Extracted from pinned McColm source, MIT-0; see analytic-extraction.json. -/
public import Mathlib

@[expose] public section

-- Lean 4.34 elaborator compatibility; kernel checking stays enabled.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex Set MeasureTheory
open scoped Topology Interval
namespace RiemannZeta.GuthMaynard
/-- The elementary Gamma integral after a positive real dilation. -/
theorem integral_cpow_mul_exp_neg_mul_Ioi_eq
    {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * Complex.exp (-(a * x))) =
      (1 / a : ℂ) ^ s * Gamma s := by
  simpa only [Complex.ofReal_neg, Complex.ofReal_mul,
    Complex.ofReal_exp] using
    Complex.integral_cpow_mul_exp_neg_mul_Ioi hs ha

/-- The dilated complex Gamma integrand is integrable on the positive
half-line. -/
theorem integrableOn_cpow_mul_exp_neg_mul_Ioi
    {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 1) * Complex.exp (-(a * x)))
      (Set.Ioi 0) := by
  let f : ℝ → ℂ := fun u => Complex.exp (-(u : ℂ))
  have hbase : MellinConvergent f s := by
    unfold MellinConvergent f
    refine (Complex.GammaIntegral_convergent hs).congr_fun ?_ measurableSet_Ioi
    intro x hx
    change ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s - 1) =
      (x : ℂ) ^ (s - 1) * Complex.exp (-(x : ℂ))
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  have hscaled : MellinConvergent (fun x => f (a * x)) s :=
    (MellinConvergent.comp_mul_left (f := f) (s := s) ha).2 hbase
  unfold MellinConvergent at hscaled
  refine hscaled.congr_fun ?_ measurableSet_Ioi
  intro x _
  simp only [f, smul_eq_mul, Complex.ofReal_mul]


end RiemannZeta.GuthMaynard
