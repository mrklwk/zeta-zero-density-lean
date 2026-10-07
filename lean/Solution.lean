module
public import DensityInterfaces.ClosedCount
public import DensityInterfaces.IEANTNSolution
public import DensityInterfaces.ANTEDBAdapter

@[expose] public section

open scoped BigOperators

theorem DensityThreeQuarters.density_bound :
    ∀ σ ε : ℝ, 3 / 4 < σ → 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) ∧
      (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        C * T ^ (2 * (1 - σ) + ε) :=
  DensityInterfaces.closed_count_density_bound
