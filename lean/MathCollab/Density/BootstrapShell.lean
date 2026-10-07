module
public import MathCollab.Density.BootstrapSupremum
public import MathCollab.Density.Comparison

@[expose] public section

open Real Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

def comparisonConstant (w : ComparisonCutoff) : ℝ := (uniform_comparison w).choose

theorem comparisonConstant_nonneg (w : ComparisonCutoff) : 0 ≤ comparisonConstant w :=
  (uniform_comparison w).choose_spec.1

theorem local_comparison_from_supremum (w : ComparisonCutoff) {κ : ℝ} (d : LargeValueData κ)
    (hW : d.W.Nonempty) {U : Finset ℝ} (hU : U ⊆ d.W) {L H : ℝ}
    (hL : (d.N : ℝ) ≤ L) (hH : 1 ≤ H) (hHT : H ≤ d.T)
    {M : ℕ} (hM : M ∈ reflectionBlocks L H) (j : ℤ) :
    completePairEnergy M (localSet U H j) ≤
      comparisonConstant w * bootstrapScalar d.T d.N d.V * (d.N : ℝ)*(M : ℝ)^2*(localSet U H j).card +
      bootstrapBound w.toReflectionCutoff d * (bootstrapScalar d.T d.N d.V)^3 *
        (localSet U H j).card * ((d.N : ℝ)^2*(M : ℝ)^2+4*(d.N : ℝ)*H) := by
  have hHp : 0 < H := by linarith
  have hNp : (0 : ℝ) < d.N := by exact_mod_cast d.N_pos
  have hLp : 0 < L := hNp.trans_le hL
  have hscale := reflection_recursive_scale d.N_pos (by linarith [d.T_ge_two]) hL hHp hHT hM
  have hMp := (reflectionBlock_scale_bounds hLp hHp hM).1
  have hUW := localSet_subset_original hU H j
  by_cases hne : (localSet U H j).Nonempty
  · have hfamily := mem_bootstrapFamily.mpr ⟨hUW, hne⟩
    have hQ := kernelEnergy_le_bootstrapBound w.toReflectionCutoff d hfamily hscale
    have hS := (uniform_comparison w).choose_spec.2 d.T d.V d.N M d.a (localSet U H j)
      d.N_pos hMp hscale.2 d.V_pos (oneSeparated_subset d.separated hUW) d.coefficients
      (fun t ht => d.large t (hUW ht))
    have hB := bootstrapBound_nonneg w.toReflectionCutoff d hW
    have hb := bootstrapScalar_nonneg d.T d.V d.N
    have hd := localSet_localDiameter_le hH U j
    have hdd : ((d.N : ℝ)*M)^2+(d.N : ℝ)*localDiameter (localSet U H j) ≤
        ((d.N : ℝ)*M)^2+4*(d.N : ℝ)*H := by nlinarith
    calc
      _ ≤ comparisonConstant w * bootstrapScalar d.T d.N d.V * (d.N : ℝ)*(M : ℝ)^2*(localSet U H j).card +
          (bootstrapScalar d.T d.N d.V)^2*kernelEnergy w.toReflectionCutoff ((d.N : ℝ)*M) (localSet U H j) := hS
      _ ≤ comparisonConstant w * bootstrapScalar d.T d.N d.V * (d.N : ℝ)*(M : ℝ)^2*(localSet U H j).card +
          (bootstrapScalar d.T d.N d.V)^2*(bootstrapBound w.toReflectionCutoff d *
            bootstrapScalar d.T d.N d.V * (localSet U H j).card *
              (((d.N : ℝ)*M)^2+4*(d.N : ℝ)*H)) := by
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact hQ.trans (mul_le_mul_of_nonneg_left hdd (by positivity))
      _ = _ := by ring
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne, completePairEnergy, Finset.sum_empty,
      Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, add_zero, le_refl]

theorem reflectionBlock_scaled_square {L H : ℝ} (hL : 0 < L) (hH : 0 < H)
    {M : ℕ} (hM : M ∈ reflectionBlocks L H) : (L^2/H)*(M : ℝ)^2 ≤ 16*H := by
  have hh := (le_div_iff₀ (by positivity : 0 < Real.pi*L)).1
    (reflectionBlock_scale_bounds hL hH hM).2.2
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hc := mul_le_mul_of_nonneg_left hpi (show 0 ≤ (M : ℝ)*L by positivity)
  have hm : (M : ℝ)*L ≤ 4*H := by nlinarith
  have hs := pow_le_pow_left₀ (show 0 ≤ (M : ℝ)*L by positivity) hm 2
  have he : (L^2/H)*(M : ℝ)^2 = ((M : ℝ)*L)^2/H := by ring
  rw [he]
  exact (div_le_iff₀ hH).2 (by nlinarith)

theorem localReflectionEnergy_from_supremum (w : ComparisonCutoff) {κ : ℝ} (d : LargeValueData κ)
    (hW : d.W.Nonempty) {U : Finset ℝ} (hU : U ⊆ d.W) {L H : ℝ}
    (hL : (d.N : ℝ) ≤ L) (hH : 1 ≤ H) (hHT : H ≤ d.T) :
    (L^2/H)*localReflectionEnergy L H U ≤
      30*(U.card : ℝ)*(16*comparisonConstant w*bootstrapScalar d.T d.N d.V*(d.N : ℝ)*H +
        bootstrapBound w.toReflectionCutoff d*(bootstrapScalar d.T d.N d.V)^3*
          (16*(d.N : ℝ)^2*H+4*(d.N : ℝ)*L^2)) := by
  let b := bootstrapScalar d.T d.N d.V
  let B := bootstrapBound w.toReflectionCutoff d
  let C := comparisonConstant w
  let F := 16*C*b*(d.N : ℝ)*H+B*b^3*(16*(d.N : ℝ)^2*H+4*(d.N : ℝ)*L^2)
  have hHp : 0 < H := by linarith
  have hLp : 0 < L := (by exact_mod_cast d.N_pos : (0 : ℝ) < d.N).trans_le hL
  have hb : 0 ≤ b := bootstrapScalar_nonneg d.T d.V d.N
  have hB : 0 ≤ B := bootstrapBound_nonneg w.toReflectionCutoff d hW
  have hC : 0 ≤ C := comparisonConstant_nonneg w
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hblock (M : ℕ) (hM : M ∈ reflectionBlocks L H) (j : ℤ) :
      (L^2/H)*completePairEnergy M (localSet U H j) ≤ F*(localSet U H j).card := by
    have hs := mul_le_mul_of_nonneg_left
      (local_comparison_from_supremum w d hW hU hL hH hHT hM j)
      (show 0 ≤ L^2/H by positivity)
    have hm := reflectionBlock_scaled_square hLp hHp hM
    have hc := mul_le_mul_of_nonneg_left hm
      (show 0 ≤ C*b*(d.N : ℝ)*(localSet U H j).card by positivity)
    have hr := mul_le_mul_of_nonneg_left hm
      (show 0 ≤ B*b^3*(localSet U H j).card*(d.N : ℝ)^2 by positivity)
    have he : (L^2/H)*H = L^2 := by field_simp
    have hz := congrArg (fun x : ℝ => B*b^3*(localSet U H j).card*4*(d.N : ℝ)*x) he
    dsimp [C, b, B, F] at *
    nlinarith
  have hjcard : (∑ j ∈ localIndices U H, ((localSet U H j).card : ℝ)) = 3*(U.card : ℝ) := by
    exact_mod_cast (sum_card_localSet (U := U) hHp)
  calc
    _ = ∑ M ∈ reflectionBlocks L H, ∑ j ∈ localIndices U H,
        (L^2/H)*completePairEnergy M (localSet U H j) := by
      simp only [localReflectionEnergy, tsum_completePairEnergy_localSet hHp, Finset.mul_sum]
    _ ≤ ∑ _M ∈ reflectionBlocks L H, ∑ j ∈ localIndices U H, F*(localSet U H j).card :=
      Finset.sum_le_sum (fun M hM => Finset.sum_le_sum (fun j _ => hblock M hM j))
    _ = ((reflectionBlocks L H).card : ℝ)*(F*(3*(U.card : ℝ))) := by
      simp only [← Finset.mul_sum, hjcard, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 10*(F*(3*(U.card : ℝ))) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast reflectionBlocks_card_le hLp hHp) (by positivity)
    _ = _ := by dsimp [F, C, b, B]; ring

/-- Actual reflection and comparison feed the actual finite supremum; neither is a premise. -/
theorem bootstrap_one_shell (w : ComparisonCutoff) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ {κ : ℝ} (d : LargeValueData κ), d.W.Nonempty →
      ∀ (U : Finset ℝ) (L H : ℝ), U ⊆ d.W → (d.N : ℝ) ≤ L → 1 ≤ H → H ≤ d.T →
      shellEnergy w.toReflectionCutoff L H U ≤
        C*bootstrapScalar d.T d.N d.V*(d.N : ℝ)*H*U.card +
        C*bootstrapBound w.toReflectionCutoff d*(bootstrapScalar d.T d.N d.V)^3*U.card*
          ((d.N : ℝ)^2*H+(d.N : ℝ)*L^2) + E*d.T^(-100 : ℝ) := by
  let R := (20000/Real.pi^2)*(mellinMass w.toReflectionCutoff)^2
  let C₀ := comparisonConstant w
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC₀ : 0 ≤ C₀ := comparisonConstant_nonneg w
  obtain ⟨E, hE, hrefl⟩ := uniform_reflection_application w.toReflectionCutoff
  refine ⟨480*R*(C₀+1), E, by positivity, hE, ?_⟩
  intro κ d hW U L H hU hL hH hHT
  have hHp : 0 < H := by linarith
  have hb := bootstrapScalar_nonneg d.T d.V d.N
  have hB := bootstrapBound_nonneg w.toReflectionCutoff d hW
  have hd : intervalSpan U ≤ d.T := by
    have hh := (d.local_card_le hU).2
    dsimp [localDiameter] at hh
    linarith
  have hs := (hrefl d.T L H U d.T_ge_two (d.scale_lower.trans hL) hHp
    (oneSeparated_subset d.separated hU) hd).1
  have hi := mul_le_mul_of_nonneg_left
    (localReflectionEnergy_from_supremum w d hW hU hL hH hHT) hR
  have he : R*(L^2/H)*localReflectionEnergy L H U = R*((L^2/H)*localReflectionEnergy L H U) := by ring
  change shellEnergy w.toReflectionCutoff L H U ≤ R*(L^2/H)*localReflectionEnergy L H U + _ at hs
  rw [he] at hs
  have hc : 0 ≤ R*bootstrapScalar d.T d.N d.V*(d.N : ℝ)*H*U.card := by positivity
  have hx : 0 ≤ R*bootstrapBound w.toReflectionCutoff d*(bootstrapScalar d.T d.N d.V)^3*U.card*
      ((d.N : ℝ)^2*H+(d.N : ℝ)*L^2) := by positivity
  have hy : 0 ≤ R*bootstrapBound w.toReflectionCutoff d*(bootstrapScalar d.T d.N d.V)^3*U.card*
      ((d.N : ℝ)*L^2) := by positivity
  dsimp [C₀] at *
  nlinarith [mul_nonneg hC₀ hx]

end MathCollab.Density
