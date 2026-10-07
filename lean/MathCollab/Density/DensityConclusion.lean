module
public import MathCollab.Density.DensitySlabBound
public import MathCollab.Density.DensityDyadicSummation

@[expose] public section

open Real Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Explicit counting loss, fixed before all scales and zeros. -/
def densityCountingEta (σ ε : ℝ) : ℝ := min ((σ-3/4)/16) (ε/24)

theorem densityCountingEta_margins {σ ε : ℝ} (hσ : 3/4 < σ) (hε : 0 < ε) :
    0 < densityCountingEta σ ε ∧
      8*densityCountingEta σ ε < σ-3/4 ∧ 12*densityCountingEta σ ε < ε := by
  unfold densityCountingEta
  have hleft := min_le_left ((σ-3/4)/16) (ε/24)
  have hright := min_le_right ((σ-3/4)/16) (ε/24)
  exact ⟨lt_min (by positivity) (by positivity), by linarith, by linarith⟩

/-- The original count is empty to the right of the open critical strip. -/
theorem zetaDensityCount_eq_zero_of_one_le {σ : ℝ} (hσ : 1 ≤ σ) (T : ℝ) :
    zetaDensityCount σ T = 0 := by
  have he : zetaZeroFinset σ (-T) T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    have hh := mem_zetaZeroFinset.mp hρ
    linarith [hh.1.2.2,hh.2.1]
  simp [zetaDensityCount,zetaSlabCount,he]

/-- Complete density consequence with one clearly isolated pointwise input.
The count is the original actual-zero analytic-multiplicity count, and the
constant precedes every height, including the bounded range. -/
theorem zeta_density_bound_of_weyl {σ ε η₀ Cw : ℝ}
    (hσ : 3/4 < σ) (hε : 0 < ε)
    (hη₀ : 0 ≤ η₀) (hη₀' : η₀ < 1/48) (hCw : 0 ≤ Cw)
    (hW : ∀ t : ℝ, ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ Cw*(1+|t|)^(1/6+η₀)) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ C*T^(2*(1-σ)+ε) := by
  by_cases hσ' : σ < 1
  · have hm := densityCountingEta_margins hσ hε
    obtain ⟨A,hA,hslab⟩ := zetaSlab_density_bound_of_weyl hσ hσ' hm.1 hm.2.1
      hη₀ hη₀' hCw hW
    have hp : 0 < 2*(1-σ)+12*densityCountingEta σ ε := by linarith [hm.1]
    obtain ⟨C,hC,hall⟩ := zetaDensity_bound_of_eventual_slabs hp hA hslab
    refine ⟨C,hC,?_⟩
    intro T hT
    exact (hall T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ T) (by linarith [hm.2.2])) hC.le)
  · refine ⟨1,by norm_num,?_⟩
    intro T hT
    rw [zetaDensityCount_eq_zero_of_one_le (not_lt.mp hσ')]
    simp only [Nat.cast_zero,one_mul]
    positivity

end MathCollab.Density
