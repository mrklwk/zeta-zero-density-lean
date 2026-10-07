module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.Objects
public import WeylPort.Reflection
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Tactic

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Functional equation and conjugation for the actual AFE remainder

The zeta conjugation theorem is reused directly from the existing node-71 foundation.
The chi convention is the literal product in the paper, with principal complex powers.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex
open scoped BigOperators ComplexConjugate

/-- Combining the two positive real bases preserves the paper's chi convention. -/
theorem chi_eq_two_mul (s : ℂ) :
    chi s = 2 * (2 * (Real.pi : ℂ)) ^ (s - 1) * Gamma (1 - s) *
      sin ((Real.pi : ℂ) * s / 2) := by
  have hpow := mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2)
    Real.pi_pos.le (s - 1)
  norm_num only [ofReal_ofNat] at hpow
  rw [hpow]
  have htwo : (2 : ℂ) ^ s = 2 * (2 : ℂ) ^ (s - 1) := by
    conv_lhs => rw [show s = s - 1 + 1 by ring]
    rw [cpow_add _ _ (by norm_num), cpow_one]
    ring
  simp only [chi, htwo]
  ring

/-- The functional equation in the orientation required by the paper's actual chi factor. -/
theorem zeta_eq_chi_mul_zeta_one_sub {s : ℂ} (hs : s.im ≠ 0) :
    riemannZeta s = chi s * riemannZeta (1 - s) := by
  have hne (n : ℕ) : 1 - s ≠ -(n : ℂ) := by
    intro h
    have hi := congrArg Complex.im h
    simp only [sub_im, one_im, neg_im, natCast_im] at hi
    exact hs (by linarith)
  have hne1 : 1 - s ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [sub_im, one_im] at hi
    exact hs (by linarith)
  have h := riemannZeta_one_sub hne hne1
  rw [show 1 - (1 - s) = s by ring, show -(1 - s) = s - 1 by ring,
    show (Real.pi : ℂ) * (1 - s) / 2 = (Real.pi : ℂ) / 2 -
      (Real.pi : ℂ) * s / 2 by ring, cos_pi_div_two_sub] at h
  rw [chi_eq_two_mul]
  exact h

/-- Conjugation commutes with a principal power of a nonnegative real base. -/
theorem conj_nonneg_cpow {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    conj ((x : ℂ) ^ s) = (x : ℂ) ^ conj s := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg hx]
    exact Real.pi_ne_zero.symm
  simpa only [conj_ofReal] using (cpow_conj (x : ℂ) s harg).symm

/-- The literal chi product commutes with conjugation. -/
theorem chi_conj (s : ℂ) : chi (conj s) = conj (chi s) := by
  have htwo := conj_nonneg_cpow (by norm_num : (0 : ℝ) ≤ 2) s
  have hpi := conj_nonneg_cpow Real.pi_pos.le (s - 1)
  norm_num only [ofReal_ofNat] at htwo
  simp only [chi, map_mul, htwo, hpi, map_sub, map_one, ← Gamma_conj,
    ← sin_conj, map_div₀, conj_ofReal, map_ofNat]


end DhimanKadiriQuesadaHerrera2026
