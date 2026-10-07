module
public import MathCollab.Density.ZeroSeparation
public import MathCollab.Density.LargeValues

@[expose] public section

open Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- Arbitrary finite-index version of the proved conditional bridge from a finite family detecting every actual zero and a
local multiplicity bound to the proved large-values estimate. The constant
precedes the slab, ambient height, bin bound, and entire polynomial family.
No detector or local zero-count estimate is asserted by this theorem. -/
theorem zetaSlab_large_values_cover_indexed {ι : Type*} {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ lo hi H B : ℝ) (J : Finset ι)
      (N : ι → ℕ) (V : ι → ℝ) (coeff : ι → ℕ → ℂ),
      2 ≤ H → 0 ≤ B → hi ≤ lo+H →
      (∀ k : ℤ, (∑ ρ ∈ (zetaZeroFinset σ lo hi).filter
        (fun ρ => ordinateBin ρ = k), (zetaMultiplicity ρ : ℝ)) ≤ B) →
      (∀ j ∈ J, 0 < N j ∧ 0 < V j ∧ H^(1/3 : ℝ) ≤ (N j : ℝ) ∧
        (N j : ℝ) ≤ H ∧ (N j : ℝ)^(3/4+κ) ≤ V j ∧
        ∀ n ∈ Finset.Ioc (N j) (2*N j), ‖coeff j n‖ ≤ 1) →
      (∀ ρ ∈ zetaZeroFinset σ lo hi, ∃ j ∈ J,
        V j ≤ ‖detectingPolynomial (N j) (coeff j) ρ.im‖) →
      (zetaSlabCount σ lo hi : ℝ) ≤ C*B*H^ε*
        ∑ j ∈ J, ((N j : ℝ)^2/(V j)^2+(N j : ℝ)^3*Real.sqrt H/(V j)^4) := by
  classical
  obtain ⟨C, hC, hLV⟩ := large_values hκ hε
  refine ⟨2*C, by positivity, ?_⟩
  intro σ lo hi H B J N V coeff hH hB hhi hlocal hadm hcover
  obtain ⟨R, hR, hcard, hsep, hcount⟩ := zetaSlab_separated_representatives σ lo hi hB hlocal
  let W := R.image Complex.im
  let Wj := fun j => W.filter (fun t => V j ≤ ‖detectingPolynomial (N j) (coeff j) t‖)
  let F := fun j => (N j : ℝ)^2/(V j)^2+(N j : ℝ)^3*Real.sqrt H/(V j)^4
  have hWj : ∀ j ∈ J, ((Wj j).card : ℝ) ≤ C*H^ε*F j := by
    intro j hj
    obtain ⟨hN, hV, hlow, hhigh, hheight, hc⟩ := hadm j hj
    apply hLV H (V j) (N j) (coeff j) (Wj j) hH hN hV hlow hhigh hheight hc
    · refine ⟨lo, ?_⟩
      intro t ht
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp ht).1
      have hz := mem_zetaZeroFinset.mp (hR hρ)
      exact ⟨hz.2.2.1, hz.2.2.2.trans hhi⟩
    · intro t ht u hu htu
      exact hsep t (Finset.mem_filter.mp ht).1 u (Finset.mem_filter.mp hu).1 htu
    · intro t ht
      exact (Finset.mem_filter.mp ht).2
  have hsub : W ⊆ J.biUnion Wj := by
    intro t ht
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j, hj, hdetect⟩ := hcover ρ (hR hρ)
    exact Finset.mem_biUnion.mpr ⟨j, hj, Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩, hdetect⟩⟩
  have hc : (W.card : ℝ) ≤ ∑ j ∈ J, ((Wj j).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_biUnion_le)
  have hsum : (W.card : ℝ) ≤ C*H^ε*∑ j ∈ J, F j := by
    calc
      _ ≤ ∑ j ∈ J, ((Wj j).card : ℝ) := hc
      _ ≤ ∑ j ∈ J, C*H^ε*F j := Finset.sum_le_sum hWj
      _ = _ := by rw [Finset.mul_sum]
  rw [← hcard] at hcount
  calc
    _ ≤ 2*B*(W.card : ℝ) := hcount
    _ ≤ 2*B*(C*H^ε*∑ j ∈ J, F j) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp [F]; ring

end MathCollab.Density
