module
public import IEANTN.Vocabulary.Zeta

@[expose] public section

/-!
# DensityThreeQuarters.v1

For every σ>3/4 and ε>0, one existential positive C bounds IEANTN's
open-rectangle, multiplicity-weighted zero count for every real T≥2.
No explicit numerical constant, endpoint σ=3/4, or ε=0 is asserted.
This conclusion has no network hypotheses and imports no proof module.
-/

namespace DensityThreeQuarters.v1

def density_bound : Prop :=
  ∀ σ ε : ℝ, 3 / 4 < σ → 0 < ε →
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      IEANTN.zetaN' σ T ≤ C * T ^ (2 * (1 - σ) + ε)

end DensityThreeQuarters.v1
