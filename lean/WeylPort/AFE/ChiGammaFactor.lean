module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.ChiReflection

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Exact gamma factor and the relative error in Lemma 7

The denominator is handled for both signs of the height. The literal exponential
in Lemma 7 is retained; it gives a large, but valid, bound at negative heights.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex
open scoped ComplexConjugate

/-- Principal powers on the negative imaginary axis have the explicit phase used by the AFE. -/
theorem cpow_two_pi_div_I (s : ℂ) :
    (2 * (Real.pi : ℂ) / I) ^ (s - 1) =
      (2 * (Real.pi : ℂ)) ^ (s - 1) *
        exp (-(Real.pi : ℂ) / 2 * I * (s - 1)) := by
  have hb : 2 * (Real.pi : ℂ) ≠ 0 := mul_ne_zero (by norm_num)
    (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hid : 2 * (Real.pi : ℂ) / I = ((2 * Real.pi : ℝ) : ℂ) * (-I) := by
    simp [div_eq_mul_inv, Complex.inv_I]
  rw [hid, cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast Real.two_pi_pos.ne')
    (neg_ne_zero.mpr I_ne_zero)), log_ofReal_mul Real.two_pi_pos
      (neg_ne_zero.mpr I_ne_zero), log_neg_I, add_mul, exp_add]
  rw [cpow_def_of_ne_zero hb]
  congr 1
  · rw [show 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_log Real.two_pi_pos.le]
  · congr 1
    ring

/-- The exact identity underlying Lemma 7, before division by its nonzero factor. -/
theorem gamma_factor_mul_one_sub_exp (s : ℂ) :
    (Gamma (1 - s) * (2 * (Real.pi : ℂ) / I) ^ (s - 1)) *
      (1 - exp ((Real.pi : ℂ) * s * I)) = chi s := by
  have he : exp (-(Real.pi : ℂ) / 2 * I * (s - 1)) =
      exp (-((Real.pi : ℂ) * s / 2) * I) * I := by
    rw [show -(Real.pi : ℂ) / 2 * I * (s - 1) =
      -((Real.pi : ℂ) * s / 2) * I + (Real.pi : ℂ) / 2 * I by ring,
      exp_add, exp_pi_div_two_mul_I]
  have heprod : exp (-((Real.pi : ℂ) * s / 2) * I) *
      exp ((Real.pi : ℂ) * s * I) = exp (((Real.pi : ℂ) * s / 2) * I) := by
    rw [← exp_add]
    congr 1
    ring
  rw [cpow_two_pi_div_I, he, chi_eq_two_mul, Complex.sin]
  linear_combination -Gamma (1 - s) * (2 * (Real.pi : ℂ)) ^ (s - 1) * I * heprod

/-- The norm of the exponential denominator term records the signed height exactly. -/
theorem norm_exp_pi_mul_I (s : ℂ) :
    ‖exp ((Real.pi : ℂ) * s * I)‖ = Real.exp (-Real.pi * s.im) := by
  rw [norm_exp]
  congr 1
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
    zero_mul, mul_one, sub_zero, add_zero, zero_sub]
  ring

/-- The denominator remains uniformly separated from zero for either sign of height. -/
theorem one_sub_exp_neg_abs_le_norm (s : ℂ) :
    1 - Real.exp (-Real.pi * |s.im|) ≤ ‖1 - exp ((Real.pi : ℂ) * s * I)‖ := by
  rcases le_total 0 s.im with hs | hs
  · rw [abs_of_nonneg hs]
    simpa only [norm_one, norm_exp_pi_mul_I] using
      (norm_sub_norm_le (1 : ℂ) (exp ((Real.pi : ℂ) * s * I)))
  · rw [abs_of_nonpos hs]
    have h := norm_sub_norm_le (exp ((Real.pi : ℂ) * s * I)) (1 : ℂ)
    rw [norm_exp_pi_mul_I, norm_one, norm_sub_rev] at h
    have hp := Real.add_one_le_exp (-Real.pi * s.im)
    have hn := Real.add_one_le_exp (Real.pi * s.im)
    rw [neg_mul_neg]
    linarith

/-- The relative error is an actual complex number with the exact source denominator. -/
noncomputable def gammaChiError (s : ℂ) : ℂ :=
  exp ((Real.pi : ℂ) * s * I) / (1 - exp ((Real.pi : ℂ) * s * I))

/-- The denominator lower bound uses the positive threshold, independently of the height sign. -/
theorem gammaChi_denominator_bound {s : ℂ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (ht : t₀ ≤ |s.im|) :
    0 < 1 - Real.exp (-Real.pi * t₀) ∧
      1 - Real.exp (-Real.pi * t₀) ≤ ‖1 - exp ((Real.pi : ℂ) * s * I)‖ := by
  have he : Real.exp (-Real.pi * t₀) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  refine ⟨by linarith, ?_⟩
  have hm : Real.exp (-Real.pi * |s.im|) ≤ Real.exp (-Real.pi * t₀) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  linarith [one_sub_exp_neg_abs_le_norm s]

/-- Lemma 7's printed signed-height error bound is valid for both signs of the height. -/
theorem norm_gammaChiError_le {s : ℂ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (ht : t₀ ≤ |s.im|) :
    ‖gammaChiError s‖ ≤ Real.exp (-Real.pi * s.im) /
      (1 - Real.exp (-Real.pi * t₀)) := by
  obtain ⟨hp, hle⟩ := gammaChi_denominator_bound ht₀ ht
  rw [gammaChiError, norm_div, norm_exp_pi_mul_I]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hp hle

/-- Lemma 7 is an exact identity plus a separately proved relative-error estimate. -/
theorem gamma_factor_eq_chi_mul_one_add {s : ℂ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (ht : t₀ ≤ |s.im|) :
    Gamma (1 - s) * (2 * (Real.pi : ℂ) / I) ^ (s - 1) =
      chi s * (1 + gammaChiError s) := by
  have hd : 1 - exp ((Real.pi : ℂ) * s * I) ≠ 0 := by
    apply norm_pos_iff.mp
    exact lt_of_lt_of_le (gammaChi_denominator_bound ht₀ ht).1
      (gammaChi_denominator_bound ht₀ ht).2
  rw [gammaChiError]
  have he : 1 + exp ((Real.pi : ℂ) * s * I) /
      (1 - exp ((Real.pi : ℂ) * s * I)) =
      (1 - exp ((Real.pi : ℂ) * s * I))⁻¹ := by
    calc
      _ = ((1 - exp ((Real.pi : ℂ) * s * I)) + exp ((Real.pi : ℂ) * s * I)) /
          (1 - exp ((Real.pi : ℂ) * s * I)) := by rw [add_div, div_self hd]
      _ = _ := by rw [sub_add_cancel, one_div]
  rw [he, ← div_eq_mul_inv]
  exact (eq_div_iff hd).mpr (gamma_factor_mul_one_sub_exp s)

/-- The literal Lemma-7 product and its relative-error bound are obtained together. -/
theorem gamma_factor_lemma_seven {s : ℂ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (ht : t₀ ≤ |s.im|) :
    ∃ ε : ℂ, Gamma (1 - s) * (2 * (Real.pi : ℂ) / I) ^ (s - 1) =
      chi s * (1 + ε) ∧
      ‖ε‖ ≤ Real.exp (-Real.pi * s.im) / (1 - Real.exp (-Real.pi * t₀)) :=
  ⟨gammaChiError s, gamma_factor_eq_chi_mul_one_add ht₀ ht,
    norm_gammaChiError_le ht₀ ht⟩

/-- The conjugate branch uses the positive imaginary base at negative heights. -/
theorem gamma_factor_conjugate_branch {s : ℂ} {t₀ : ℝ} (ht₀ : 0 < t₀)
    (ht : t₀ ≤ -s.im) :
    ∃ ε : ℂ, Gamma (1 - s) * (2 * (Real.pi : ℂ) / (-I)) ^ (s - 1) =
      chi s * (1 + ε) ∧
      ‖ε‖ ≤ Real.exp (-Real.pi * |s.im|) / (1 - Real.exp (-Real.pi * t₀)) := by
  have him : s.im < 0 := by linarith
  have hnonneg : 0 ≤ -s.im := by linarith
  have hc : t₀ ≤ |(conj s).im| := by
    simpa only [conj_im, abs_of_nonneg hnonneg] using ht
  refine ⟨conj (gammaChiError (conj s)), ?_, ?_⟩
  · have h := congrArg conj (gamma_factor_eq_chi_mul_one_add ht₀ hc)
    have harg : (2 * (Real.pi : ℂ) / I).arg ≠ Real.pi := by
      intro heq
      have hneg := (arg_eq_pi_iff.mp heq).1
      norm_num [div_eq_mul_inv, Complex.inv_I] at hneg
    have hp' : conj ((2 * (Real.pi : ℂ) / I) ^ (conj s - 1)) =
        (2 * (Real.pi : ℂ) / (-I)) ^ (s - 1) := by
      have hpow := conj_cpow (2 * (Real.pi : ℂ) / I) (s - 1) harg
      simpa only [map_div₀, map_mul, map_ofNat, conj_ofReal, conj_I,
        map_sub, map_one] using hpow.symm
    simp only [map_mul, hp', ← Gamma_conj, map_sub, map_one, conj_conj,
      ← chi_conj, map_add] at h
    exact h
  · rw [norm_conj]
    simpa only [conj_im, abs_of_neg him] using norm_gammaChiError_le ht₀ hc

end DhimanKadiriQuesadaHerrera2026
