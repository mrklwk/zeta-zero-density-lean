module
public import DensityInterfaces.ClosedCount

@[expose] public section

open scoped BigOperators
set_option autoImplicit false

namespace DensityInterfaces

/-- The conventional positive-height zero count, with both the real-part
cutoff and upper height cutoff closed, and analytic multiplicity retained. -/
theorem positive_count_density_bound : ∀ σ ε : ℝ, 3 / 4 < σ → 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔
        riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ 0 < ρ.im ∧ ρ.im ≤ T) ∧
      (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        C * T ^ (2 * (1 - σ) + ε) := by
  classical
  intro σ ε hσ hε
  obtain ⟨C, hC, hbound⟩ := closed_count_density_bound σ ε hσ hε
  refine ⟨C, hC, fun T hT => ?_⟩
  obtain ⟨Z, hZ, hsum⟩ := hbound T hT
  refine ⟨Z.filter (fun ρ => 0 < ρ.im), ?_, ?_⟩
  · intro ρ
    simp only [Finset.mem_filter, hZ]
    constructor
    · rintro ⟨⟨hz, hre, hheight⟩, hpos⟩
      exact ⟨hz, hre, hpos, (le_abs_self ρ.im).trans hheight⟩
    · rintro ⟨hz, hre, hpos, hheight⟩
      exact ⟨⟨hz, hre, by simpa only [abs_of_pos hpos] using hheight⟩, hpos⟩
  · exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (by intros; positivity)).trans hsum

end DensityInterfaces
