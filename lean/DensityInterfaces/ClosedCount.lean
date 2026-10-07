module
public import MathCollab.Density.DensityTheorem

@[expose] public section

/-! # A literal public statement with no project-defined counting function -/

open scoped BigOperators
set_option autoImplicit false

namespace DensityInterfaces

open MathCollab.Density

theorem closed_count_density_bound : ∀ σ ε : ℝ, 3 / 4 < σ → 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) ∧
      (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        C * T ^ (2 * (1 - σ) + ε) := by
  intro σ ε hσ hε
  obtain ⟨C, hC, hbound⟩ := zeta_density_bound hσ hε
  refine ⟨C, hC, fun T hT => ⟨zetaZeroFinset σ (-T) T, ?_, ?_⟩⟩
  · intro ρ
    rw [mem_zetaDensityFinset]
    constructor
    · rintro ⟨hz, hre, hheight⟩
      exact ⟨hz.1, hre, hheight⟩
    · rintro ⟨hz, hre, hheight⟩
      have hupper : ρ.re < 1 := by
        by_contra h
        exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
      exact ⟨⟨hz, by linarith, hupper⟩, hre, hheight⟩
  · simpa only [zetaDensityCount, zetaSlabCount, zetaMultiplicity, Nat.cast_sum]
      using hbound T hT

end DensityInterfaces
