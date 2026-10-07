module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Actual AFE weights satisfy the additional Part-I hypotheses

The phase scale is `t/(2*pi)` in the applications. These proofs include `sigma=0`,
where the weight is constant, and do not assume the desired Poisson estimate.
-/

namespace DhimanKadiriQuesadaHerrera2026

/-- The actual real power weight used in both approximate functional equations. -/
noncomputable def afeWeight (sigma x : ℝ) : ℝ := x ^ (-sigma)

/-- The logarithmic phase, with its positive height scale supplied explicitly. -/
noncomputable def afePhase (c x : ℝ) : ℝ := c * Real.log x

/-- The exact power-weight derivative on the positive half-line. -/
theorem afeWeight_hasDerivAt (sigma : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (afeWeight sigma) (-sigma * x ^ (-sigma - 1)) x :=
  Real.hasDerivAt_rpow_const (Or.inl hx.ne')

/-- The exact logarithmic phase derivative. -/
theorem afePhase_hasDerivAt (c : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (afePhase c) (c / x) x := by
  change HasDerivAt (fun y : ℝ => c * Real.log y) (c / x) x
  convert (Real.hasDerivAt_log hx.ne').const_mul c using 1
  rw [div_eq_mul_inv]

/-- The power weight is positive on its actual domain. -/
theorem afeWeight_pos (sigma : ℝ) {x : ℝ} (hx : 0 < x) : 0 < afeWeight sigma x :=
  Real.rpow_pos_of_pos hx _

/-- Nonnegative exponents give the decreasing weights required by the source. -/
theorem afeWeight_antitone {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    AntitoneOn (afeWeight sigma) (Set.Ioi 0) := by
  intro x hx y _ hxy
  exact Real.rpow_le_rpow_of_nonpos hx hxy (neg_nonpos.mpr hsigma)

/-- Absolute value of the true derivative, including the zero-weight-derivative boundary. -/
theorem abs_deriv_afeWeight {sigma x : ℝ} (hsigma : 0 ≤ sigma) (hx : 0 < x) :
    |deriv (afeWeight sigma) x| = sigma * x ^ (-sigma - 1) := by
  rw [(afeWeight_hasDerivAt sigma hx).deriv, abs_mul, abs_neg, abs_of_nonneg hsigma,
    abs_of_pos (Real.rpow_pos_of_pos hx _)]

/-- First accepted repair condition: the absolute derivative is nonincreasing. -/
theorem abs_deriv_afeWeight_antitone {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    AntitoneOn (fun x => |deriv (afeWeight sigma) x|) (Set.Ioi 0) := by
  intro x hx y hy hxy
  dsimp only
  rw [abs_deriv_afeWeight hsigma hx, abs_deriv_afeWeight hsigma hy]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)) hsigma

/-- Normalize the actual derivative quotient before proving its monotonicity. -/
theorem afe_derivative_quotient {sigma c x : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 ≤ c)
    (hx : 0 < x) :
    |deriv (afeWeight sigma) x| / (1 + deriv (afePhase c) x) =
      sigma * x ^ (-sigma) / (x + c) := by
  rw [abs_deriv_afeWeight hsigma hx, (afePhase_hasDerivAt c hx).deriv,
    Real.rpow_sub_one hx.ne']
  have hxc : x + c ≠ 0 := ne_of_gt (by positivity)
  field_simp

/-- Second accepted repair condition for the actual logarithmic phase at `N=0`. -/
theorem afe_derivative_quotient_antitone {sigma c : ℝ} (hsigma : 0 ≤ sigma) (hc : 0 ≤ c) :
    AntitoneOn (fun x => |deriv (afeWeight sigma) x| / (1 + deriv (afePhase c) x))
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  dsimp only
  rw [afe_derivative_quotient hsigma hc hx, afe_derivative_quotient hsigma hc hy]
  apply div_le_div₀ (by positivity)
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)) hsigma)
    (by positivity) (by linarith)

/-- The actual AFE weight/phase pair satisfies both added hypotheses, including sigma zero. -/
theorem afe_weights_satisfy_accepted_partI_hypotheses {sigma c : ℝ}
    (hsigma : 0 ≤ sigma) (hc : 0 ≤ c) :
    AntitoneOn (fun x => |deriv (afeWeight sigma) x|) (Set.Ioi 0) ∧
      AntitoneOn (fun x => |deriv (afeWeight sigma) x| / (1 + deriv (afePhase c) x))
        (Set.Ioi 0) :=
  ⟨abs_deriv_afeWeight_antitone hsigma, afe_derivative_quotient_antitone hsigma hc⟩

end DhimanKadiriQuesadaHerrera2026
