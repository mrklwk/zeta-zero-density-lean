module
public import MathCollab.Density.ReflectionApplication
public import MathCollab.Density.ProductGrouping

@[expose] public section

open Real Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

theorem LargeValueData.scalar_lower {κ : ℝ} (d : LargeValueData κ) (hW : d.W.Nonempty) :
    1/(d.N : ℝ) ≤ bootstrapScalar d.T d.N d.V := by
  have hN : (0 : ℝ) < d.N := by exact_mod_cast d.N_pos
  have hV := d.V_pos
  have hvn := d.height_le_length hW
  have hdelta : (1 : ℝ) ≤ divisorMaximum d.T := by
    exact_mod_cast divisorMaximum_ge_one (show 0 ≤ d.T by linarith [d.T_ge_two])
  calc
    _ ≤ (d.N : ℝ)/d.V^2 := (div_le_div_iff₀ hN (by positivity)).2 (by nlinarith)
    _ ≤ bootstrapScalar d.T d.N d.V := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      nlinarith

theorem LargeValueData.scalar_pos {κ : ℝ} (d : LargeValueData κ) (hW : d.W.Nonempty) :
    0 < bootstrapScalar d.T d.N d.V :=
  (one_div_pos.mpr (by exact_mod_cast d.N_pos)).trans_le (d.scalar_lower hW)

/-- All nonempty subsets form a finite localization family closed under the reflection windows. -/
def bootstrapFamily (W : Finset ℝ) : Finset (Finset ℝ) := W.powerset.filter Finset.Nonempty

theorem mem_bootstrapFamily {W U : Finset ℝ} :
    U ∈ bootstrapFamily W ↔ U ⊆ W ∧ U.Nonempty := by
  simp only [bootstrapFamily, Finset.mem_filter, Finset.mem_powerset]

theorem bootstrapFamily_nonempty {W : Finset ℝ} (hW : W.Nonempty) :
    (bootstrapFamily W).Nonempty := ⟨W, mem_bootstrapFamily.mpr ⟨Finset.Subset.refl _, hW⟩⟩

theorem localSet_subset_original {W U : Finset ℝ} (hU : U ⊆ W) (H : ℝ) (j : ℤ) :
    localSet U H j ⊆ W := (Finset.filter_subset _ _).trans hU

theorem bootstrapFamily_local_closed {W U : Finset ℝ} (hU : U ∈ bootstrapFamily W)
    (H : ℝ) (j : ℤ) (hne : (localSet U H j).Nonempty) :
    localSet U H j ∈ bootstrapFamily W :=
  mem_bootstrapFamily.mpr ⟨localSet_subset_original (mem_bootstrapFamily.mp hU).1 H j, hne⟩

/-- The normalization has a uniform positive lower bound on the actual recursion domain. -/
theorem LargeValueData.normalization_lower {κ : ℝ} (d : LargeValueData κ)
    {U : Finset ℝ} (hU : U ∈ bootstrapFamily d.W) {L : ℝ} (hNL : (d.N : ℝ) ≤ L) :
    (d.N : ℝ) ≤ bootstrapScalar d.T d.N d.V * U.card * (L^2+(d.N : ℝ)*localDiameter U) := by
  obtain ⟨hUW, hUn⟩ := mem_bootstrapFamily.mp hU
  have hW := hUn.mono hUW
  have hN : (0 : ℝ) < d.N := by exact_mod_cast d.N_pos
  have hb := d.scalar_lower hW
  have hbp := d.scalar_pos hW
  have hr : (1 : ℝ) ≤ U.card := by exact_mod_cast Finset.card_pos.mpr hUn
  have hd := localDiameter_ge_one U
  have hbr : bootstrapScalar d.T d.N d.V ≤ bootstrapScalar d.T d.N d.V*U.card := by nlinarith
  have hL : 0 ≤ L := hN.le.trans hNL
  have hnle : (d.N : ℝ)^2 ≤ L^2+(d.N : ℝ)*localDiameter U := by nlinarith
  calc
    _ = (1/(d.N : ℝ))*(d.N : ℝ)^2 := by field_simp
    _ ≤ bootstrapScalar d.T d.N d.V*U.card*(L^2+(d.N : ℝ)*localDiameter U) :=
      mul_le_mul (hb.trans hbr) hnle (sq_nonneg _) (by positivity)

end MathCollab.Density
