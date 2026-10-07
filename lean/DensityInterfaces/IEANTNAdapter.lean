module
public import MathCollab.Density.DensityTheorem
public import IEANTN.Vocabulary.Zeta

@[expose] public section

/-!
# The actual IEANTN open-rectangle count

The upstream vocabulary is pinned in `third_party/ieantn`. Finiteness and
summability are proved before using its `tsum`; meromorphic integer orders
are identified with the analytic multiplicities of the audited theorem.
-/

open Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section

namespace DensityInterfaces

open MathCollab.Density

theorem ieantn_order_eq {ρ : ℂ} (hρ : ρ ≠ 1) :
    IEANTN.zetaOrder ρ = (zetaMultiplicity ρ : ℤ) := by
  unfold IEANTN.zetaOrder
  rw [(analyticOn_riemannZeta ρ hρ).meromorphicOrderAt_eq,
    ← zetaMultiplicity_cast hρ, ENat.map_natCast, WithTop.untopD_coe]

theorem ieantn_rectangle_subset {σ T : ℝ} (hσ : 0 ≤ σ) (hT : 0 ≤ T) :
    IEANTN.zetaZeroesIn (Ioo σ 1) (Ioo 0 T) ⊆ zetaZeroRegion σ (-T) T := by
  intro ρ hρ
  obtain ⟨⟨hs, h1⟩, ⟨h0, hTρ⟩, hz⟩ := hρ
  exact ⟨⟨hz, lt_of_le_of_lt hσ hs, h1⟩, hs.le,
    le_trans (neg_nonpos.mpr hT) h0.le, hTρ.le⟩

theorem ieantn_rectangle_finite {σ T : ℝ} (hσ : 0 ≤ σ) (hT : 0 ≤ T) :
    (IEANTN.zetaZeroesIn (Ioo σ 1) (Ioo 0 T)).Finite :=
  (zetaZeroRegion_finite σ (-T) T).subset (ieantn_rectangle_subset hσ hT)

theorem ieantn_count_summable {σ T : ℝ} (hσ : 0 ≤ σ) (hT : 0 ≤ T) :
    Summable (fun ρ : IEANTN.zetaZeroesIn (Ioo σ 1) (Ioo 0 T) =>
      (1 : ℝ) * (IEANTN.zetaOrder ρ : ℤ)) := by
  let := (ieantn_rectangle_finite hσ hT).fintype
  exact summable_of_hasFiniteSupport (Set.toFinite _)

theorem ieantn_count_le {σ T : ℝ} (hσ : 0 ≤ σ) (hT : 0 ≤ T) :
    IEANTN.zetaN' σ T ≤ (zetaDensityCount σ T : ℝ) := by
  classical
  let hf := ieantn_rectangle_finite hσ hT
  let := hf.fintype
  have hmem : ∀ ρ : ℂ, ρ ∈ hf.toFinset ↔
      ρ ∈ IEANTN.zetaZeroesIn (Ioo σ 1) (Ioo 0 T) := fun _ => hf.mem_toFinset
  have hsub : hf.toFinset ⊆ zetaZeroFinset σ (-T) T := by
    intro ρ hρ
    exact mem_zetaZeroFinset.mpr (ieantn_rectangle_subset hσ hT (hmem ρ |>.mp hρ))
  have hord : ∀ ρ : IEANTN.zetaZeroesIn (Ioo σ 1) (Ioo 0 T),
      (IEANTN.zetaOrder ρ : ℝ) = (zetaMultiplicity ρ : ℝ) := by
    intro ρ
    rw [ieantn_order_eq (nontrivialZetaZero_ne_one
      (ieantn_rectangle_subset hσ hT ρ.property).1)]
    simp
  calc
    IEANTN.zetaN' σ T =
        ∑ ρ : IEANTN.zetaZeroesIn (Ioo σ 1) (Ioo 0 T),
          (zetaMultiplicity ρ : ℝ) := by
      simp only [IEANTN.zetaN', IEANTN.zetaZeroesSum, one_mul, tsum_fintype]
      exact Finset.sum_congr rfl fun ρ _ => hord ρ
    _ = ∑ ρ ∈ hf.toFinset, (zetaMultiplicity ρ : ℝ) :=
      (Finset.sum_subtype hf.toFinset hmem
        (fun ρ : ℂ => (zetaMultiplicity ρ : ℝ))).symm
    _ ≤ ∑ ρ ∈ zetaZeroFinset σ (-T) T, (zetaMultiplicity ρ : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ = (zetaDensityCount σ T : ℝ) := by
      simp [zetaDensityCount, zetaSlabCount]

/-- The audited density theorem in the exact current IEANTN vocabulary.
The positive constant is existential and precedes every real `T ≥ 2`. -/
theorem ieantn_density_bound {σ ε : ℝ} (hσ : 3 / 4 < σ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 2 ≤ T →
      IEANTN.zetaN' σ T ≤ C * T ^ (2 * (1 - σ) + ε) := by
  obtain ⟨C, hC, hbound⟩ := zeta_density_bound hσ hε
  exact ⟨C, hC, fun T hT =>
    (ieantn_count_le (by linarith) (by linarith)).trans (hbound T hT)⟩

end DensityInterfaces
