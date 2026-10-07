module
public import WeylPort.ShortSum
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

open Complex Finset
open scoped BigOperators ComplexConjugate

namespace WeylPort

noncomputable def criticalPoint (t : ℝ) : ℂ := (1/2:ℂ) + (t:ℂ)*I

theorem one_sub_criticalPoint (t : ℝ) :
    1 - criticalPoint t = conj (criticalPoint t) := by
  apply Complex.ext <;> norm_num [criticalPoint]

theorem criticalPoint_neg (t : ℝ) :
    criticalPoint (-t) = conj (criticalPoint t) := by
  apply Complex.ext <;> simp [criticalPoint]

theorem criticalTerm_neg (t : ℝ) (n : ℕ) :
    criticalTerm (-t) n = conj (criticalTerm t n) := by
  have ha : (n:ℂ).arg ≠ Real.pi := by simp [Real.pi_ne_zero.symm]
  have hc := Complex.cpow_conj (n:ℂ) (-criticalPoint t) ha
  change (n:ℂ)^(-criticalPoint (-t)) = conj ((n:ℂ)^(-criticalPoint t))
  rw [criticalPoint_neg]
  simpa only [map_neg, map_natCast] using hc

theorem norm_critical_sum_neg (t : ℝ) (N : ℕ) :
    ‖∑ n ∈ Ico 1 (N+1), criticalTerm (-t) n‖ =
      ‖∑ n ∈ Ico 1 (N+1), criticalTerm t n‖ := by
  simp_rw [criticalTerm_neg]
  rw [← map_sum, Complex.norm_conj]

/-- The dual AFE polynomial has exactly the same norm as the original polynomial. -/
theorem norm_dual_critical_sum (t : ℝ) (N : ℕ) :
    ‖∑ n ∈ Ico 1 (N+1), (n:ℂ)^(criticalPoint t - 1)‖ =
      ‖∑ n ∈ Ico 1 (N+1), criticalTerm t n‖ := by
  have hexp : criticalPoint t - 1 = -criticalPoint (-t) := by
    rw [criticalPoint_neg, ← one_sub_criticalPoint]
    ring
  simp_rw [hexp]
  exact norm_critical_sum_neg t N

/-- The same explicit polynomial bound holds for both signs of the height. -/
theorem norm_critical_sum_le_log_abs (t : ℝ) (N : ℕ)
    (ht : 1 ≤ |t|) (hNt : (N:ℝ)^2 ≤ |t|) :
    ‖∑ n ∈ Ico 1 (N+1), criticalTerm t n‖ ≤
      30 * (Real.log |t| + 1) * |t| ^ (1/6:ℝ) := by
  by_cases ht0 : 0 ≤ t
  · simpa only [abs_of_nonneg ht0] using
      norm_critical_sum_le_log |t| N ht hNt
  · have hb := norm_critical_sum_le_log |t| N ht hNt
    rw [abs_of_neg (lt_of_not_ge ht0), norm_critical_sum_neg] at hb
    simpa only [abs_of_neg (lt_of_not_ge ht0)] using hb

theorem gammaReal_conj (s : ℂ) : Gammaℝ (conj s) = conj (Gammaℝ s) := by
  have ha : (Real.pi:ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_ne_zero.symm
  have hc := Complex.cpow_conj (Real.pi:ℂ) (-s/2) ha
  simp only [map_div₀, map_neg, map_ofNat, conj_ofReal] at hc
  simp only [Gammaℝ, map_mul, ← Gamma_conj, map_div₀, map_ofNat, hc]

/-- The genuine completed-zeta gamma quotient in the functional equation. -/
noncomputable def criticalGammaRatio (t : ℝ) : ℂ :=
  Gammaℝ (1 - criticalPoint t) / Gammaℝ (criticalPoint t)

theorem norm_criticalGammaRatio (t : ℝ) : ‖criticalGammaRatio t‖ = 1 := by
  have hne : Gammaℝ (criticalPoint t) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by norm_num [criticalPoint])
  rw [criticalGammaRatio, one_sub_criticalPoint, gammaReal_conj, norm_div,
    Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hne)]

/-- Actual zeta reflection, with no zeta-value nonvanishing assumption. -/
theorem riemannZeta_critical_functional_equation (t : ℝ) :
    riemannZeta (criticalPoint t) =
      criticalGammaRatio t * riemannZeta (1 - criticalPoint t) := by
  have hs : criticalPoint t ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    norm_num [criticalPoint] at this
  have hs' : 1 - criticalPoint t ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    norm_num [criticalPoint] at this
  have hne : Gammaℝ (1 - criticalPoint t) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by norm_num [criticalPoint])
  rw [riemannZeta_def_of_ne_zero hs, riemannZeta_def_of_ne_zero hs',
    completedRiemannZeta_one_sub, criticalGammaRatio]
  field_simp

/-- The product-form chi used by the source AFE is the genuine gamma quotient.
This identification uses Gamma reflection and duplication, never division by zeta. -/
theorem critical_chi_product_eq_ratio (t : ℝ) :
    (2:ℂ)^(criticalPoint t) * (Real.pi:ℂ)^(criticalPoint t - 1) *
      Gamma (1-criticalPoint t) * sin ((Real.pi:ℂ)*criticalPoint t/2) =
        criticalGammaRatio t := by
  let s := criticalPoint t
  have hs : ∀ n : ℕ, 1-s ≠ -(2*n+1) := by
    intro n he
    have hr := congrArg Complex.re he
    norm_num [s,criticalPoint] at hr
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := Gammaℝ_div_Gammaℝ_one_sub hs
  rw [show 1-(1-s) = s by ring] at h
  change (2:ℂ)^s * (Real.pi:ℂ)^(s-1) * Gamma (1-s) * sin ((Real.pi:ℂ)*s/2) =
    Gammaℝ (1-s)/Gammaℝ s
  rw [h, Gammaℂ, show -(1-s) = s-1 by ring]
  have hc : cos ((Real.pi:ℂ)*(1-s)/2) = sin ((Real.pi:ℂ)*s/2) := by
    rw [show (Real.pi:ℂ)*(1-s)/2 = (Real.pi:ℂ)/2-(Real.pi:ℂ)*s/2 by ring,
      Complex.cos_pi_div_two_sub]
  have hp : (2*(Real.pi:ℂ))^(s-1) = (2:ℂ)^(s-1)*(Real.pi:ℂ)^(s-1) := by
    simpa using Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ) ≤ 2)
      Real.pi_pos.le (s-1)
  have ht : (2:ℂ)^s = 2*(2:ℂ)^(s-1) := by
    conv_lhs => rw [show s = 1+(s-1) by ring]
    rw [Complex.cpow_add _ _ (by norm_num), Complex.cpow_one]
  rw [hc,hp,ht]
  ring

/-- Exact unit norm for the source AFE's literal product-form chi factor. -/
theorem norm_critical_chi_product (t : ℝ) :
    ‖(2:ℂ)^(criticalPoint t) * (Real.pi:ℂ)^(criticalPoint t - 1) *
      Gamma (1-criticalPoint t) * sin ((Real.pi:ℂ)*criticalPoint t/2)‖ = 1 := by
  rw [critical_chi_product_eq_ratio, norm_criticalGammaRatio]

end WeylPort
