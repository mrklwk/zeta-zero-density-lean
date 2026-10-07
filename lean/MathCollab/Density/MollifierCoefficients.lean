module
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- Real cutoffs use the natural floor; every term has positive integer index. -/
def zetaMollifier (X : ℝ) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 ⌊X⌋₊, (ArithmeticFunction.moebius d : ℂ)*(d : ℂ)^(-s)

/-- These coefficients depend on X alone, never on a zero or its real part. -/
def mollifierCoefficient (X : ℝ) (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors with d ≤ ⌊X⌋₊, ArithmeticFunction.moebius d

theorem mollifierCoefficient_eq_full {X : ℝ} {n : ℕ} (hn : (n : ℝ) ≤ X) :
    mollifierCoefficient X n = ∑ d ∈ n.divisors, ArithmeticFunction.moebius d := by
  unfold mollifierCoefficient
  rw [Finset.filter_eq_self.mpr]
  intro d hd
  exact (Nat.divisor_le hd).trans (Nat.le_floor hn)

theorem mollifierCoefficient_one {X : ℝ} (hX : 1 ≤ X) :
    mollifierCoefficient X 1 = 1 := by
  rw [mollifierCoefficient_eq_full (by simpa using hX)]
  simp

theorem mollifierCoefficient_vanishes {X : ℝ} {n : ℕ} (hn : 2 ≤ n) (hnX : (n : ℝ) ≤ X) :
    mollifierCoefficient X n = 0 := by
  rw [mollifierCoefficient_eq_full hnX]
  have he := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.coe_zeta_mul_moebius
  simpa only [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply,
    ite_eq_right (show n ≠ 1 by omega)] using he

theorem mollifierCoefficient_abs_le (X : ℝ) (n : ℕ) :
    |mollifierCoefficient X n| ≤ (n.divisors.card : ℤ) := by
  unfold mollifierCoefficient
  calc
    _ ≤ ∑ d ∈ n.divisors with d ≤ ⌊X⌋₊, |ArithmeticFunction.moebius d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors with _d ≤ ⌊X⌋₊, (1 : ℤ) :=
      Finset.sum_le_sum fun _ _ => ArithmeticFunction.abs_moebius_le_one
    _ = ((n.divisors.filter (fun d => d ≤ ⌊X⌋₊)).card : ℤ) := by simp
    _ ≤ (n.divisors.card : ℤ) := by exact_mod_cast Finset.card_filter_le n.divisors _

theorem mollifierCoefficient_norm_le (X : ℝ) (n : ℕ) :
    ‖(mollifierCoefficient X n : ℂ)‖ ≤ (n.divisors.card : ℝ) := by
  have h := mollifierCoefficient_abs_le X n
  rw [Complex.norm_intCast]
  exact_mod_cast h

end MathCollab.Density
