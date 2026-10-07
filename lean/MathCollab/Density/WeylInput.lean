module
public import WeylPort.ActualZeta

@[expose] public section

open Complex
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The independently ported actual-zeta theorem discharges the detector's
literal all-real-height growth input, with the constant before t. -/
theorem actual_zeta_weyl_input {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ C*(1+|t|)^(1/6+η₀) := by
  obtain ⟨C,hC,hW⟩ := WeylPort.exists_riemannZeta_critical_weyl_all_heights hη₀
  refine ⟨C,hC,?_⟩
  intro t
  have hm : max 1 |t| ≤ 1+|t| := max_le (by linarith [abs_nonneg t]) (by linarith)
  exact (hW t).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hm (by linarith)) hC.le)

end MathCollab.Density
