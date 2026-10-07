module
public import MathCollab.Density.ReflectionAssembly

@[expose] public section

open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff ComplexConjugate

noncomputable section
namespace MathCollab.Density

theorem dirichletPhase_neg (x v : ℝ) : dirichletPhase x (-v) = conj (dirichletPhase x v) := by
  unfold dirichletPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem hKernel_neg (w : ReflectionCutoff) (L v : ℝ) :
    hKernel w L (-v) = conj (hKernel w L v) := by
  unfold hKernel cutoffIntegral
  rw [map_sub, Complex.conj_tsum, map_mul, Complex.conj_ofReal, ← integral_conj]
  simp only [dirichletPhase_neg, map_mul, Complex.conj_ofReal]

theorem norm_hKernel_neg (w : ReflectionCutoff) (L v : ℝ) :
    ‖hKernel w L (-v)‖ = ‖hKernel w L v‖ := by
  rw [hKernel_neg, Complex.norm_conj]

theorem shellEnergy_eq_twice_positive (w : ReflectionCutoff) (L : ℝ)
    {H : ℝ} (hH : 0 < H) (U : Finset ℝ) :
    shellEnergy w L H U = 2 * positiveShell H U (fun v => ‖hKernel w L v‖ ^ 2) := by
  have he (v : ℝ) : (if H ≤ |v| ∧ |v| < 2*H then ‖hKernel w L v‖ ^ 2 else 0) =
      (if H ≤ v ∧ v < 2*H then ‖hKernel w L v‖ ^ 2 else 0) +
      (if H ≤ -v ∧ -v < 2*H then ‖hKernel w L (-v)‖ ^ 2 else 0) := by
    by_cases hv : 0 ≤ v
    · have hn : ¬(H ≤ -v ∧ -v < 2*H) := by intro hh; linarith [hh.1]
      simp only [abs_of_nonneg hv, ite_eq_right hn, add_zero]
    · have hn : ¬(H ≤ v ∧ v < 2*H) := by intro hh; linarith [hh.1]
      simp only [abs_of_nonpos (le_of_not_ge hv), ite_eq_right hn, zero_add, norm_hKernel_neg]
  unfold shellEnergy positiveShell
  simp_rw [he, Finset.sum_add_distrib]
  have hs : (∑ t ∈ U, ∑ u ∈ U,
      if H ≤ -(t-u) ∧ -(t-u) < 2*H then ‖hKernel w L (-(t-u))‖ ^ 2 else 0) =
      ∑ t ∈ U, ∑ u ∈ U, if H ≤ t-u ∧ t-u < 2*H then ‖hKernel w L (t-u)‖ ^ 2 else 0 := by
    rw [Finset.sum_comm]
    simp only [neg_sub]
  rw [hs]
  ring

theorem positiveShell_add (H : ℝ) (U : Finset ℝ) (F G : ℝ → ℝ) :
    positiveShell H U (fun v => F v + G v) = positiveShell H U F + positiveShell H U G := by
  unfold positiveShell
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro u _
  split_ifs <;> simp

theorem positiveShell_const_le (H : ℝ) (U : Finset ℝ) {c : ℝ} (hc : 0 ≤ c) :
    positiveShell H U (fun _ => c) ≤ (U.card : ℝ)^2 * c := by
  calc
    _ ≤ ∑ t ∈ U, ∑ u ∈ U, c := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro u _
      split_ifs
      · exact le_rfl
      · exact hc
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

/-- The squared uniform error in the manuscript's real-power notation. -/
theorem error_power_eq {L : ℝ} (hL : 0 < L) (A : ℕ) :
    (L/L^A)^2 = L ^ (2 - 2*(A : ℝ)) := by
  rw [Real.rpow_sub hL]
  have he : (2 : ℝ)*(A : ℝ) = ((A*2 : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_natCast, Real.rpow_two, pow_mul, div_pow]

/-- Squared triangle inequality using the already proved fixed-band error. -/
theorem hKernel_sq_le_band_error (w : ReflectionCutoff) (L H v E : ℝ)
    (he : ‖hKernel w L v - bandContribution w L H v‖ ≤ E) :
    ‖hKernel w L v‖^2 ≤ 2*‖bandContribution w L H v‖^2 + 2*E^2 := by
  have ht : ‖hKernel w L v‖ ≤ ‖bandContribution w L H v‖ + E := by
    calc
      _ = ‖bandContribution w L H v + (hKernel w L v - bandContribution w L H v)‖ := by congr 1; ring
      _ ≤ ‖bandContribution w L H v‖ + ‖hKernel w L v - bandContribution w L H v‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl he
  have hs := pow_le_pow_left₀ (norm_nonneg _) ht 2
  nlinarith [sq_nonneg (‖bandContribution w L H v‖-E)]

/-- Exact fixed-band reflection, with a cutoff/order constant chosen before all scales and sets. -/
theorem uniform_reflection (w : ReflectionCutoff) {A : ℕ} (hA : 1 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (L H : ℝ) (U : Finset ℝ), 0 < L → 0 < H →
      shellEnergy w L H U ≤
        (20000/Real.pi^2) * (mellinMass w)^2 * (L^2/H) * localReflectionEnergy L H U +
          4*K^2*(U.card : ℝ)^2 * L ^ (2-2*(A : ℝ)) ∧
      (∑ _t ∈ U, ‖hKernel w L 0‖ ^ 2) ≤ K^2*(U.card : ℝ) * L ^ (2-2*(A : ℝ)) := by
  obtain ⟨K, hK, herr⟩ := uniform_fixedBand_and_diagonal_error w hA
  refine ⟨K, hK, ?_⟩
  intro L H U hL hH
  let E := K*L/L^A
  have he (v : ℝ) (hv : H ≤ v) (hv2 : v < 2*H) :
      ‖hKernel w L v‖^2 ≤ 2*‖bandContribution w L H v‖^2 + 2*E^2 :=
    hKernel_sq_le_band_error w L H v E (herr L H v hL hH hv hv2.le).1
  have hp : positiveShell H U (fun v => ‖hKernel w L v‖^2) ≤
      2*((5000/Real.pi^2)*(mellinMass w)^2*(L^2/H)*localReflectionEnergy L H U) +
        (U.card : ℝ)^2 * (2*E^2) := by
    calc
      _ ≤ positiveShell H U (fun v => 2*‖bandContribution w L H v‖^2 + 2*E^2) :=
        positiveShell_mono H U he
      _ = 2*positiveShell H U (fun v => ‖bandContribution w L H v‖^2) +
          positiveShell H U (fun _ => 2*E^2) := by
        rw [positiveShell_add, positiveShell_const_mul]
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_left (positiveShell_bandContribution_le w hL hH U) (by norm_num))
        (positiveShell_const_le H U (by positivity))
  have hpow : E^2 = K^2 * L ^ (2-2*(A : ℝ)) := by
    rw [← error_power_eq hL A]
    dsimp [E]
    ring
  constructor
  · rw [shellEnergy_eq_twice_positive w L hH]
    have hh := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
    rw [hpow] at hh
    convert hh using 1; ring
  · have hz : ‖hKernel w L 0‖ ≤ E := (herr L H H hL hH le_rfl (by linarith)).2
    have hz2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    have hh := Finset.sum_le_sum (s := U) (fun t _ => hz2)
    simp only [Finset.sum_const, nsmul_eq_mul] at hh ⊢
    rw [hpow] at hh
    convert hh using 1; ring

end MathCollab.Density
