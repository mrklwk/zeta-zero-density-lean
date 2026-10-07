module
public import MathCollab.Density.DensityExponentAccounting
public import MathCollab.Density.IndexedZeroLargeValues
public import MathCollab.Density.LocalZeroCount

@[expose] public section

open Real Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The actual all-zero, multiplicity-weighted positive slab satisfies the
original 12eta exponent. The sole analytic input is explicitly displayed. -/
theorem zetaSlab_density_bound_of_weyl {σ η η₀ Cw : ℝ}
    (hσ : 3/4 < σ) (hσ' : σ < 1) (hη : 0 < η) (hmargin : 8*η < σ-3/4)
    (hη₀ : 0 ≤ η₀) (hη₀' : η₀ < 1/48) (hCw : 0 ≤ Cw)
    (hW : ∀ t : ℝ, ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ Cw*(1+|t|)^(1/6+η₀)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (zetaSlabCount σ T (2*T) : ℝ) ≤ C*T^(2*(1-σ)+12*η) := by
  let κ := (σ-3/4)/2
  have hκ : 0 < κ := by dsimp [κ]; linarith
  have hm : 3/4+κ ≤ σ-4*η := by dsimp [κ]; linarith
  obtain ⟨Cv, hCv, hbound⟩ := zetaSlab_large_values_cover_indexed
    (ι := (ℕ × ℕ) × ℕ) hκ hη
  obtain ⟨Cb, hCb, hlocal⟩ := zeta_local_multiplicity_bound
  refine ⟨30720*Cv*Cb, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ),
    poweredDetectorFamily_admissible hη hm,
    poweredDetectorFamily_cover_of_zeta_bound hη hη₀ hη₀' hCw hW,
    density_family_sum_eventually hη hσ.le hσ'.le] with T hT hadm hcover hsum
  have hlog : 0 ≤ Real.log (2*T) := Real.log_nonneg (by linarith)
  have hcount := hbound σ T (2*T) (densityAmbient T) (Cb*Real.log (2*T))
    (poweredDetectorIndices T) (poweredDetectorScale T)
    (fun p => (poweredDetectorScale T p : ℝ)^σ*T^(-2*η))
    (poweredDetectorFamilyCoeff η T) hadm.1 (by positivity) hadm.2.1
    (hlocal σ T hσ.le hT) hadm.2.2.2
    (by
      intro ρ hρ
      obtain ⟨hz, hβ, hγ, hγ'⟩ := mem_zetaZeroFinset.mp hρ
      have habs : |ρ.im| = ρ.im := abs_of_nonneg (by linarith)
      exact hcover σ ρ hσ.le hβ hz.2.2 (by rwa [habs]) (by rwa [habs]) hz.1)
  have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ Cv*Cb by positivity)
  calc
    _ ≤ _ := hcount
    _ = (Cv*Cb)*(Real.log (2*T)*(densityAmbient T)^η*
        (∑ p ∈ poweredDetectorIndices T,
          ((poweredDetectorScale T p : ℝ)^2/((poweredDetectorScale T p : ℝ)^σ*T^(-2*η))^2+
          (poweredDetectorScale T p : ℝ)^3*Real.sqrt (densityAmbient T)/
            ((poweredDetectorScale T p : ℝ)^σ*T^(-2*η))^4))) := by ring
    _ ≤ (Cv*Cb)*(30720*T^(2*(1-σ)+12*η)) := hh
    _ = _ := by ring

end MathCollab.Density
