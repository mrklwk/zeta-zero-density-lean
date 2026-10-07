module
public import MathCollab.Density.DensityConclusion
public import MathCollab.Density.WeylInput

@[expose] public section

open Real Complex
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The density bound for every sigma>3/4 and epsilon>0, with a constant uniform
in T>=2. The count includes every actual nontrivial zeta zero with sigma<=Re(rho)
and -T<=Im(rho)<=T, weighted by its analytic multiplicity. No analytic premise
remains: the all-height classical Weyl bound is supplied by the verified port. -/
theorem zeta_density_bound {σ ε : ℝ} (hσ : 3/4 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(2*(1-σ)+ε) := by
  obtain ⟨Cw,hCw,hW⟩ := actual_zeta_weyl_input (by norm_num : (0 : ℝ) < 1/96)
  exact zeta_density_bound_of_weyl hσ hε (by norm_num : (0 : ℝ) ≤ 1/96)
    (by norm_num : (1/96 : ℝ) < 1/48) hCw.le hW

end MathCollab.Density
