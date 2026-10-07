module
public import MathCollab.Density.MollifierCoefficients
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Telescoping square-root bound, including the empty cutoff. -/
theorem sum_inv_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (1 / Real.sqrt (n : ℝ)) ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N+1)]
    have hp : 0 < Real.sqrt (N+1 : ℝ) := Real.sqrt_pos.2 (by positivity)
    have hs := Real.sq_sqrt (show 0 ≤ (N : ℝ) by positivity)
    have hs' := Real.sq_sqrt (show 0 ≤ (N+1 : ℝ) by positivity)
    have hm : Real.sqrt (N : ℝ) ≤ Real.sqrt (N+1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
    have hd : 1 / Real.sqrt (N+1 : ℝ) ≤
        2*(Real.sqrt (N+1 : ℝ)-Real.sqrt (N : ℝ)) := by
      apply (div_le_iff₀ hp).2
      nlinarith [sq_nonneg (Real.sqrt (N+1 : ℝ)-Real.sqrt (N : ℝ))]
    push_cast
    linarith

/-- Uniform on the whole half-plane Re(s)>=1/2, with the natural floor cutoff. -/
theorem norm_zetaMollifier_le_two_sqrt {X : ℝ} {s : ℂ}
    (hX : 0 ≤ X) (hs : 1/2 ≤ s.re) : ‖zetaMollifier X s‖ ≤ 2*Real.sqrt X := by
  unfold zetaMollifier
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊X⌋₊,
        ‖(ArithmeticFunction.moebius d : ℂ)*(d : ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊X⌋₊, (1 / Real.sqrt (d : ℝ)) := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
      have hm : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hdpos, Complex.neg_re]
      calc
        _ ≤ (d : ℝ)^(-s.re) := by nlinarith [Real.rpow_nonneg (show 0 ≤ (d : ℝ) by positivity) (-s.re)]
        _ ≤ (d : ℝ)^(-(1/2 : ℝ)) := Real.rpow_le_rpow_of_exponent_le hdreal (by linarith)
        _ = _ := by rw [Real.rpow_neg (by positivity), Real.sqrt_eq_rpow]; simp only [one_div]
    _ ≤ 2*Real.sqrt (⌊X⌋₊ : ℝ) := sum_inv_sqrt_le _
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Nat.floor_le hX)) (by norm_num)

end MathCollab.Density
