module
public import GuthMaynard.WeylExplicit

@[expose] public section

open Complex Finset Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Critical-line consequences of the Weyl estimate

The finite Abel lemma below transfers uniform bounds for unweighted phase
prefixes to monotone nonnegative weights.  It is then applied to the actual
`n^(-1/2-it)` critical-line weight.
-/

theorem norm_weighted_sum_le_of_antitone
    (f : Nat -> Real) (g : Nat -> Complex) (N : Nat) (B : Real)
    (hN : 0 < N)
    (hf : forall i, i < N -> 0 <= f i)
    (hanti : forall i, i + 1 < N -> f (i + 1) <= f i)
    (hpartial : forall j, j <= N -> ‖∑ i ∈ Finset.range j, g i‖ <= B) :
    ‖∑ i ∈ Finset.range N, f i • g i‖ <= f 0 * B := by
  have hparts := Finset.sum_Ico_by_parts f g hN
  rw [Finset.range_eq_Ico]
  calc
    ‖∑ i ∈ Finset.Ico 0 N, f i • g i‖ =
        ‖f (N - 1) • (∑ i ∈ Finset.range N, g i) -
          f 0 • (∑ i ∈ Finset.range 0, g i) -
          ∑ i ∈ Finset.Ico 0 (N - 1),
            (f (i + 1) - f i) • (∑ j ∈ Finset.range (i + 1), g j)‖ :=
      congrArg norm hparts
    _ = ‖(f (N - 1) : Complex) * (∑ i ∈ Finset.range N, g i) -
        ∑ i ∈ Finset.Ico 0 (N - 1),
          ((f (i + 1) - f i : Real) : Complex) *
            (∑ j ∈ Finset.range (i + 1), g j)‖ := by
      simp only [Finset.sum_range_zero, Complex.real_smul, mul_zero, sub_zero]
    _ <= ‖(f (N - 1) : Complex) * (∑ i ∈ Finset.range N, g i)‖ +
        ‖∑ i ∈ Finset.Ico 0 (N - 1),
          ((f (i + 1) - f i : Real) : Complex) * (∑ j ∈ Finset.range (i + 1), g j)‖ :=
      norm_sub_le _ _
    _ <= f (N - 1) * B +
        ∑ i ∈ Finset.Ico 0 (N - 1), (f i - f (i + 1)) * B := by
      apply add_le_add
      · rw [norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hf (N - 1) (by omega))]
        exact mul_le_mul_of_nonneg_left (hpartial N le_rfl) (hf (N - 1) (by omega))
      · calc
          ‖∑ i ∈ Finset.Ico 0 (N - 1),
              ((f (i + 1) - f i : Real) : Complex) *
                (∑ j ∈ Finset.range (i + 1), g j)‖ <=
              ∑ i ∈ Finset.Ico 0 (N - 1),
                ‖((f (i + 1) - f i : Real) : Complex) *
                  (∑ j ∈ Finset.range (i + 1), g j)‖ := norm_sum_le _ _
          _ <= ∑ i ∈ Finset.Ico 0 (N - 1), (f i - f (i + 1)) * B := by
            apply Finset.sum_le_sum
            intro i hi
            have hi' := Finset.mem_Ico.mp hi
            rw [norm_mul, norm_real, Real.norm_eq_abs,
              abs_of_nonpos (sub_nonpos.mpr (hanti i (by omega)))]
            rw [neg_sub]
            exact mul_le_mul_of_nonneg_left (hpartial (i + 1) (by omega))
              (sub_nonneg.mpr (hanti i (by omega)))
    _ = f 0 * B := by
      have htel : ∑ i ∈ Finset.Ico 0 (N - 1), (f i - f (i + 1)) =
          f 0 - f (N - 1) := by
        rw [Nat.Ico_zero_eq_range, Finset.sum_range_sub']
      rw [← Finset.sum_mul, htel]
      ring

theorem logarithmicSum_eq_sum_range (t : Real) (A N : Nat) :
    logarithmicSum t A (A + N) =
      ∑ n ∈ Finset.range N, unitaryPhase (logarithmicPhase t (A + n)) := by
  unfold logarithmicSum phaseSum
  rw [Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left, Nat.cast_add]

/-- The actual critical-line Dirichlet block on `[A, A + N)`. -/
noncomputable def criticalLineWeylBlock (Y : Real) (A N : Nat) : Complex :=
  ∑ n ∈ Finset.range N,
    (1 / Real.sqrt (A + n) : Real) •
      unitaryPhase (logarithmicPhase (Y ^ 3) (A + n))

theorem criticalLineTerm_eq_cpow (Y : Real) (m : Nat) (hm : 0 < m) :
    (1 / Real.sqrt m : Real) • unitaryPhase (logarithmicPhase (Y ^ 3) m) =
      (m : Complex) ^ (-((1 / 2 : Complex) + (Y ^ 3 : Complex) * I)) := by
  have hw : (1 / Real.sqrt m : Real) =
      (m : Real) ^ (-(1 / 2 : Real)) := by
    rw [Real.sqrt_eq_rpow, one_div, Real.rpow_neg (Nat.cast_nonneg m)]
  rw [Complex.real_smul, unitaryPhase_logarithmicPhase_eq_cpow _ _ hm, hw]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg m)]
  simp only [Complex.ofReal_natCast]
  rw [← Complex.cpow_add _ _ (by exact_mod_cast Nat.ne_of_gt hm)]
  congr 2
  push_cast
  ring

theorem criticalLineWeylBlock_eq_cpow
    (Y : Real) (A N : Nat) (hA : 0 < A) :
    criticalLineWeylBlock Y A N =
      ∑ n ∈ Finset.range N,
        (A + n : Complex) ^ (-((1 / 2 : Complex) + (Y ^ 3 : Complex) * I)) := by
  unfold criticalLineWeylBlock
  apply Finset.sum_congr rfl
  intro n _hn
  simpa only [Nat.cast_add] using criticalLineTerm_eq_cpow Y (A + n) (by omega)

/-- Abel summation transfers the uniform prefix Weyl estimate to the genuine
`n^(-1/2-it)` critical-line weight. -/
theorem norm_criticalLineWeylBlock_le
    (Y : Real) (A N : Nat) (hY : 1 <= Y) (hA : 0 < A) (hN : 0 < N)
    (hYA : Y <= A) (hAY : (A : Real) ^ 2 <= Y ^ 3) (hNA : N <= A) :
    ‖criticalLineWeylBlock Y A N‖ <= 30 * Real.sqrt Y := by
  let f : Nat -> Real := fun n => 1 / Real.sqrt (A + n)
  let g : Nat -> Complex := fun n =>
    unitaryPhase (logarithmicPhase (Y ^ 3) (A + n))
  have hweighted := norm_weighted_sum_le_of_antitone f g N
    (30 * Real.sqrt ((A : Real) * Y)) hN
    (fun i _hi => by dsimp only [f]; positivity)
    (fun i _hi => by
      dsimp only [f]
      apply one_div_le_one_div_of_le
      · positivity
      · apply Real.sqrt_le_sqrt
        exact_mod_cast (show A + i <= A + (i + 1) by omega))
    (fun j hj => by
      dsimp only [g]
      rw [← logarithmicSum_eq_sum_range]
      exact logarithmic_weyl_exponent_pair_prefix Y A j hY hA hYA hAY
        (hj.trans hNA))
  change ‖criticalLineWeylBlock Y A N‖ <= _
  rw [show criticalLineWeylBlock Y A N = ∑ n ∈ Finset.range N, f n • g n by rfl]
  have hbase : Real.sqrt ((A : Real) * Y) =
      Real.sqrt A * Real.sqrt Y := by
    rw [Real.sqrt_mul (Nat.cast_nonneg A)]
  have hsqrtA : 0 < Real.sqrt (A : Real) := Real.sqrt_pos.2 (Nat.cast_pos.mpr hA)
  have hsimplify : f 0 * (30 * Real.sqrt ((A : Real) * Y)) =
      30 * Real.sqrt Y := by
    dsimp only [f]
    simp only [Nat.cast_zero, add_zero]
    rw [hbase]
    field_simp [hsqrtA.ne']
  rw [hsimplify] at hweighted
  exact hweighted

/-- A zeta block with an arbitrary nonnegative real-part weight. -/
noncomputable def weightedWeylBlock
    (σ t : ℝ) (A N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    ((A + n : ℝ) ^ (-σ) : ℝ) •
      unitaryPhase (logarithmicPhase t (A + n))

theorem weightedWeylBlock_eq_cpow
    (σ t : ℝ) (A N : ℕ) (hA : 0 < A) :
    weightedWeylBlock σ t A N =
      ∑ n ∈ Finset.range N,
        (A + n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * I)) := by
  unfold weightedWeylBlock
  apply Finset.sum_congr rfl
  intro n _
  have hm : 0 < A + n := by omega
  have hmNe : ((A + n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Complex.real_smul]
  have hReal : ((A + n : ℕ) : ℝ) = (A : ℝ) + (n : ℝ) := by norm_num
  have hComplex : ((A + n : ℕ) : ℂ) = (A : ℂ) + (n : ℂ) := by norm_num
  rw [← hReal, ← hComplex]
  rw [unitaryPhase_logarithmicPhase_eq_cpow t (A + n) hm]
  rw [Complex.ofReal_cpow (Nat.cast_nonneg (A + n))]
  simp only [Complex.ofReal_natCast]
  have hNeg : (((-σ : ℝ) : ℂ)) = -(σ : ℂ) := by norm_num
  rw [hNeg]
  rw [← Complex.cpow_add _ _ hmNe]
  congr 2
  ring

/-- The uniform-prefix Weyl estimate transferred by Abel summation to the
weight `n⁻ˢ` for every `σ ≥ 0`. -/
theorem norm_weightedWeylBlock_le
    (σ Y : ℝ) (A N : ℕ) (hσ : 0 ≤ σ)
    (hY : 1 ≤ Y) (hA : 0 < A) (hN : 0 < N)
    (hYA : Y ≤ A) (hAY : (A : ℝ) ^ 2 ≤ Y ^ 3) (hNA : N ≤ A) :
    ‖weightedWeylBlock σ (Y ^ 3) A N‖ ≤
      (A : ℝ) ^ (-σ) * (30 * Real.sqrt ((A : ℝ) * Y)) := by
  let f : ℕ → ℝ := fun n => (A + n : ℝ) ^ (-σ)
  let g : ℕ → ℂ := fun n =>
    unitaryPhase (logarithmicPhase (Y ^ 3) (A + n))
  have hweighted := norm_weighted_sum_le_of_antitone f g N
    (30 * Real.sqrt ((A : ℝ) * Y)) hN
    (fun i _ => by dsimp only [f]; positivity)
    (fun i _ => by
      dsimp only [f]
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · exact_mod_cast (show A + i ≤ A + (i + 1) by omega)
      · linarith)
    (fun j hj => by
      dsimp only [g]
      rw [← logarithmicSum_eq_sum_range]
      exact logarithmic_weyl_exponent_pair_prefix Y A j hY hA hYA hAY
        (hj.trans hNA))
  change ‖weightedWeylBlock σ (Y ^ 3) A N‖ ≤ _
  rw [show weightedWeylBlock σ (Y ^ 3) A N =
      ∑ n ∈ Finset.range N, f n • g n by rfl]
  simpa only [f, Nat.cast_zero, add_zero] using hweighted

end RiemannZeta.GuthMaynard
