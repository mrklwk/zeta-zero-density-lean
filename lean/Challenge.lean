module
public import Mathlib

@[expose] public section

/-!
# Zeta density for σ>3/4

`Z` is exactly the finite set of all zeta zeros with Re(ρ)≥σ and
|Im(ρ)|≤T. Both boundary cutoffs are included. Each zero contributes its
analytic vanishing order, so this is a multiplicity count, not a count of
distinct heights. No project-defined predicate hides the zero region.

For each σ>3/4 and ε>0, the constant C is existential, positive, and chosen
before every real T≥2. No numerical value of C is supplied.

The endpoint σ=3/4 and the case ε=0 are excluded.

The single `sorry` below is an intentional Comparator specification.
`Solution` proves the same declaration and never imports this module.
-/

open scoped BigOperators

theorem DensityThreeQuarters.density_bound :
    ∀ σ ε : ℝ, 3 / 4 < σ → 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T → ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ riemannZeta ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T) ∧
      (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤
        C * T ^ (2 * (1 - σ) + ε) := by
  sorry
