module
public import MathCollab.Density.BandEnergy
public import MathCollab.Density.DyadicBlocks
public import MathCollab.Density.LocalCover

@[expose] public section

open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff ComplexConjugate

noncomputable section
namespace MathCollab.Density

theorem norm_bandPhaseSum_sq_le_blocks {L H : ℝ} (hL : 0 < L) (hH : 0 < H) (v r : ℝ) :
    ‖bandPhaseSum L H v r‖ ^ 2 ≤
      10 * ∑ M ∈ reflectionBlocks L H, ‖blockPolynomial L H M r v‖ ^ 2 := by
  have he : bandPhaseSum L H v r = ∑ j ∈ dyadicExponents L H,
      dirichletPhase (((2^j : ℕ) : ℝ)*L) (-v) * blockPolynomial L H (2^j) r v := by
    rw [bandPhaseSum, sum_reflectionBand_eq_nat]
    simp only [Int.cast_natCast]
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun m hm => (mem_dyadicExponents L H _).2 ⟨m, hm, rfl⟩)
      (fun m : ℕ => dirichletPhase ((m : ℝ)*L) (r-v))]
    apply Finset.sum_congr rfl
    intro j _
    exact fiber_phaseSum_eq hL H v r j
  have hn : ‖bandPhaseSum L H v r‖ ≤
      ∑ j ∈ dyadicExponents L H, ‖blockPolynomial L H (2^j) r v‖ := by
    rw [he]
    simpa only [norm_mul, norm_dirichletPhase, one_mul] using
      norm_sum_le (dyadicExponents L H)
        (fun j => dirichletPhase (((2^j : ℕ) : ℝ)*L) (-v) * blockPolynomial L H (2^j) r v)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (dyadicExponents L H)
    (fun _ => (1 : ℝ)) (fun j => ‖blockPolynomial L H (2^j) r v‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  have hcard : ((dyadicExponents L H).card : ℝ) ≤ 10 := by exact_mod_cast dyadicExponents_card_le hL hH
  rw [sum_reflectionBlocks]
  exact ((pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs).trans
    (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

theorem complete_pairs_block_le (L H : ℝ) (M : ℕ) (r : ℝ) (U : Finset ℝ) :
    (∑ t ∈ U, ∑ u ∈ U, ‖blockPolynomial L H M r (t-u)‖ ^ 2) ≤ completePairEnergy M U := by
  have hh := completePairEnergy_coefficient_domination M U (blockCoefficient L H r)
    (fun q _ => norm_blockCoefficient_le L H r q)
  rw [Finset.sum_comm]
  simpa only [blockPolynomial, neg_sub] using hh

/-- Local covering is applied before complete-pair coefficient domination. -/
theorem close_pairs_block_le_local (L : ℝ) {H : ℝ} (hH : 0 < H)
    (M : ℕ) (r : ℝ) (U : Finset ℝ) :
    (∑ t ∈ U, ∑ u ∈ U, if |t-u| < 2*H then
      ‖blockPolynomial L H M r (t-u)‖ ^ 2 else 0) ≤
      ∑' j : ℤ, completePairEnergy M (localSet U H j) := by
  rw [tsum_completePairEnergy_localSet hH]
  exact (close_pairs_le_local_pairs hH
    (fun t u => ‖blockPolynomial L H M r (t-u)‖ ^ 2) (fun _ _ => sq_nonneg _)).trans
    (Finset.sum_le_sum fun j _ => complete_pairs_block_le L H M r (localSet U H j))

def localReflectionEnergy (L H : ℝ) (U : Finset ℝ) : ℝ :=
  ∑ M ∈ reflectionBlocks L H, ∑' j : ℤ, completePairEnergy M (localSet U H j)

def positiveShell (H : ℝ) (U : Finset ℝ) (F : ℝ → ℝ) : ℝ :=
  ∑ t ∈ U, ∑ u ∈ U, if H ≤ t-u ∧ t-u < 2*H then F (t-u) else 0

theorem localReflectionEnergy_nonneg (L H : ℝ) (U : Finset ℝ) :
    0 ≤ localReflectionEnergy L H U := by
  apply Finset.sum_nonneg
  intro M _
  apply tsum_nonneg
  intro j
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem positiveShell_bandPhaseSum_le {L H : ℝ} (hL : 0 < L) (hH : 0 < H)
    (r : ℝ) (U : Finset ℝ) :
    positiveShell H U (fun v => ‖bandPhaseSum L H v r‖ ^ 2) ≤
      10 * localReflectionEnergy L H U := by
  unfold positiveShell
  calc
    _ ≤ ∑ t ∈ U, ∑ u ∈ U, 10 * ∑ M ∈ reflectionBlocks L H,
        if |t-u| < 2*H then ‖blockPolynomial L H M r (t-u)‖ ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro u _
      by_cases hs : H ≤ t-u ∧ t-u < 2*H
      · have hp : 0 < t-u := hH.trans_le hs.1
        have hc : |t-u| < 2*H := by rw [abs_of_pos hp]; exact hs.2
        simpa only [ite_eq_left hs, ite_eq_left hc] using norm_bandPhaseSum_sq_le_blocks hL hH (t-u) r
      · rw [ite_eq_right hs]
        apply mul_nonneg (by norm_num)
        exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
    _ = 10 * ∑ M ∈ reflectionBlocks L H, ∑ t ∈ U, ∑ u ∈ U,
        if |t-u| < 2*H then ‖blockPolynomial L H M r (t-u)‖ ^ 2 else 0 := by
      simp only [Finset.mul_sum]
      simp_rw [Finset.sum_comm (s := U) (t := reflectionBlocks L H)]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum (fun M _ => close_pairs_block_le_local L hH M r U)

/-- The finite shell sum and integral commute using proved integrability for each summand. -/
theorem positiveShell_integral {H : ℝ} (U : Finset ℝ) (F : ℝ → ℝ → ℝ)
    (hi : ∀ v, Integrable (F v)) :
    positiveShell H U (fun v => ∫ r, F v r) = ∫ r, positiveShell H U (fun v => F v r) := by
  unfold positiveShell
  symm
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro t _
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro u _
      by_cases hh : H ≤ t-u ∧ t-u < 2*H <;> simp [hh]
    · intro u _
      by_cases hh : H ≤ t-u ∧ t-u < 2*H
      · simpa only [ite_eq_left hh] using hi (t-u)
      · simp only [ite_eq_right hh]
        exact integrable_zero ℝ ℝ volume
  · intro t _
    apply integrable_finsetSum
    intro u _
    by_cases hh : H ≤ t-u ∧ t-u < 2*H
    · simpa only [ite_eq_left hh] using hi (t-u)
    · simp only [ite_eq_right hh]
      exact integrable_zero ℝ ℝ volume

theorem integrable_positiveShell {H : ℝ} (U : Finset ℝ) (F : ℝ → ℝ → ℝ)
    (hi : ∀ v, Integrable (F v)) :
    Integrable (fun r => positiveShell H U (fun v => F v r)) := by
  apply integrable_finsetSum
  intro t _
  apply integrable_finsetSum
  intro u _
  by_cases hh : H ≤ t-u ∧ t-u < 2*H
  · simpa only [ite_eq_left hh] using hi (t-u)
  · simp only [ite_eq_right hh]
    exact integrable_zero ℝ ℝ volume

theorem positiveShell_const_mul (H : ℝ) (U : Finset ℝ) (c : ℝ) (F : ℝ → ℝ) :
    positiveShell H U (fun v => c * F v) = c * positiveShell H U F := by
  unfold positiveShell
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> simp

theorem positiveShell_mono (H : ℝ) (U : Finset ℝ) {F G : ℝ → ℝ}
    (h : ∀ v, H ≤ v → v < 2*H → F v ≤ G v) :
    positiveShell H U F ≤ positiveShell H U G := by
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro u _
  split_ifs with hs
  · exact h (t-u) hs.1 hs.2
  · exact le_rfl

/-- The retained band contributes the required uniform complete-pair energy. -/
theorem positiveShell_bandContribution_le (w : ReflectionCutoff) {L H : ℝ}
    (hL : 0 < L) (hH : 0 < H) (U : Finset ℝ) :
    positiveShell H U (fun v => ‖bandContribution w L H v‖ ^ 2) ≤
      (5000/Real.pi^2) * (mellinMass w)^2 * (L^2/H) * localReflectionEnergy L H U := by
  let W := mellinLine (fun x => (w x : ℂ))
  have hW : Integrable W := integrable_mellin_line_one w.complex_smooth w.complex_support
  have hi (v : ℝ) : Integrable (fun r => ‖W r‖ * ‖bandPhaseSum L H v r‖ ^ 2) :=
    integrable_weighted_norm_sq hW (measurable_bandPhaseSum L H v).aestronglyMeasurable
      (norm_bandPhaseSum_le L H v)
  have hint : positiveShell H U (fun v => ∫ r, ‖W r‖ * ‖bandPhaseSum L H v r‖ ^ 2) ≤
      mellinMass w * (10 * localReflectionEnergy L H U) := by
    rw [positiveShell_integral U _ hi]
    have he (r : ℝ) : positiveShell H U (fun v => ‖W r‖ * ‖bandPhaseSum L H v r‖ ^ 2) =
        ‖W r‖ * positiveShell H U (fun v => ‖bandPhaseSum L H v r‖ ^ 2) :=
      positiveShell_const_mul H U _ _
    simp_rw [he]
    change (∫ r, _) ≤ (∫ r, ‖W r‖) * _
    rw [← integral_mul_const]
    apply integral_mono_ae
    · simpa only [he] using integrable_positiveShell (H := H) U _ hi
    · exact hW.norm.mul_const _
    · filter_upwards with r
      exact mul_le_mul_of_nonneg_left (positiveShell_bandPhaseSum_le hL hH r U) (norm_nonneg _)
  have hcoef : 0 ≤ (500/Real.pi^2) * mellinMass w * (L^2/H) :=
    mul_nonneg (mul_nonneg (by positivity) (mellinMass_nonneg w)) (by positivity)
  calc
    _ ≤ positiveShell H U (fun v => ((500/Real.pi^2) * mellinMass w * (L^2/H)) *
        ∫ r, ‖W r‖ * ‖bandPhaseSum L H v r‖ ^ 2) :=
      positiveShell_mono H U (fun v _ _ => norm_bandContribution_sq_le w hL hH v)
    _ = ((500/Real.pi^2) * mellinMass w * (L^2/H)) *
        positiveShell H U (fun v => ∫ r, ‖W r‖ * ‖bandPhaseSum L H v r‖ ^ 2) :=
      positiveShell_const_mul H U _ _
    _ ≤ ((500/Real.pi^2) * mellinMass w * (L^2/H)) *
        (mellinMass w * (10 * localReflectionEnergy L H U)) :=
      mul_le_mul_of_nonneg_left hint hcoef
    _ = _ := by ring

end MathCollab.Density
