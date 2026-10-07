module
public import MathCollab.Density.DensityTheorem

@[expose] public section

/-! # The left-shifted convention in ANTEDB's definition of A(σ)

The database asks for a positive δ before all heights in N(σ-δ,T).
This strengthening of the public interface follows from the open σ range.
It supplies an existential constant, not an explicit numerical constant.
-/

set_option autoImplicit false

namespace DensityInterfaces

open MathCollab.Density

theorem antedb_shifted_density_bound {σ ε : ℝ} (hσ : 3 / 4 < σ) (hε : 0 < ε) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount (σ - δ) T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) := by
  let δ := min ((σ - 3 / 4) / 2) (ε / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδσ : δ ≤ (σ - 3 / 4) / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  obtain ⟨C, hC, hbound⟩ :=
    zeta_density_bound (show 3 / 4 < σ - δ by linarith) (show 0 < ε / 2 by linarith)
  refine ⟨C, δ, hC, hδ, fun T hT => (hbound T hT).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- Exactly the quantifier order in the database's non-asymptotic definition:
for every ε>0 there are C,δ>0 before every real T≥C. -/
theorem antedb_density_exponent_two {σ : ℝ} (hσ : 3 / 4 < σ) :
    ∀ ε : ℝ, 0 < ε → ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ T : ℝ, C ≤ T →
      (zetaDensityCount (σ - δ) T : ℝ) ≤ C * T ^ (2 * (1 - σ) + ε) := by
  intro ε hε
  obtain ⟨C, δ, hC, hδ, hbound⟩ := antedb_shifted_density_bound hσ hε
  refine ⟨max C 2, δ, lt_of_lt_of_le hC (le_max_left _ _), hδ, fun T hT => ?_⟩
  have hT2 : 2 ≤ T := (le_max_right _ _).trans hT
  exact (hbound T hT2).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
    (Real.rpow_nonneg (by linarith) _))

end DensityInterfaces
