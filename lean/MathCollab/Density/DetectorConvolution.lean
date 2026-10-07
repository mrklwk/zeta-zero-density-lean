module
public import MathCollab.Density.FixedDetectorCover

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The actual block coefficients as a finite arithmetic function. -/
def detectorBlockCoefficients (T : ℝ) (N j : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n ∈ Finset.Ioc N (2*N) then detectorTaylorCoefficient T N j n else 0
  map_zero' := by simp

theorem detectorBlockCoefficients_apply (T : ℝ) (N j n : ℕ) :
    detectorBlockCoefficients T N j n =
      if n ∈ Finset.Ioc N (2*N) then detectorTaylorCoefficient T N j n else 0 := rfl

theorem detectorBlockCoefficients_norm_le {T : ℝ} {N : ℕ}
    (hT : 0 < T) (hN : 0 < N) (j n : ℕ) :
    ‖detectorBlockCoefficients T N j n‖ ≤ (n.divisors.card : ℝ) := by
  rw [detectorBlockCoefficients_apply]
  split_ifs with hn
  · exact norm_detectorTaylorCoefficient_le hT hN hn j
  · simp

/-- Direct divisor-power domination of genuine Dirichlet convolution powers.
For k<=4 this gives exponent <=8 and the required uniform subpower bound. -/
theorem arithmeticFunction_pow_norm_le {f : ArithmeticFunction ℂ}
    (hf : ∀ n : ℕ, ‖f n‖ ≤ (n.divisors.card : ℝ)) (k n : ℕ) :
    ‖(f^k) n‖ ≤ (n.divisors.card : ℝ)^(2*k) := by
  induction k generalizing n with
  | zero => simp only [pow_zero, ArithmeticFunction.one_apply, mul_zero]; split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply]
    have hb : ∀ p ∈ n.divisorsAntidiagonal,
        ‖(f^k) p.1*f p.2‖ ≤ (n.divisors.card : ℝ)^(2*k+1) := by
      intro p hp
      obtain ⟨he, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      have hd1 : p.1 ∣ n := ⟨p.2, he.symm⟩
      have hd2 : p.2 ∣ n := ⟨p.1, by rw [mul_comm]; exact he.symm⟩
      have hc1 : (p.1.divisors.card : ℝ) ≤ n.divisors.card := by
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn hd1)
      have hc2 : (p.2.divisors.card : ℝ) ≤ n.divisors.card := by
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn hd2)
      rw [norm_mul, pow_succ]
      exact mul_le_mul ((ih p.1).trans (pow_le_pow_left₀ (by positivity) hc1 _))
        ((hf p.2).trans hc2) (norm_nonneg _) (by positivity)
    calc
      _ ≤ ∑ p ∈ n.divisorsAntidiagonal, ‖(f^k) p.1*f p.2‖ := norm_sum_le _ _
      _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (n.divisors.card : ℝ)^(2*k+1) := Finset.sum_le_sum hb
      _ = _ := by
        rw [Finset.sum_const, ← Nat.map_div_right_divisors, Finset.card_map, nsmul_eq_mul]
        rw [show 2*(k+1) = (2*k+1)+1 by omega, pow_succ]
        ring

/-- Every nonzero convolution coefficient has the literal product support. -/
theorem detectorBlockCoefficients_pow_support (T : ℝ) (N j k n : ℕ)
    (hn : ((detectorBlockCoefficients T N j)^k) n ≠ 0) :
    0 < n ∧ n ≤ (2*N)^k := by
  induction k generalizing n with
  | zero =>
    simp only [pow_zero, ArithmeticFunction.one_apply] at hn
    split_ifs at hn with he
    · subst n; simp
    · exact False.elim (hn rfl)
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply] at hn
    obtain ⟨p, hp, hmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have ha : ((detectorBlockCoefficients T N j)^k) p.1 ≠ 0 := left_ne_zero_of_mul hmul
    have hb : detectorBlockCoefficients T N j p.2 ≠ 0 := right_ne_zero_of_mul hmul
    have hmem : p.2 ∈ Finset.Ioc N (2*N) := by
      by_contra h
      exact hb (by simp [detectorBlockCoefficients_apply, h])
    have hi := ih p.1 ha
    have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
    refine ⟨Nat.pos_of_ne_zero (Nat.mem_divisorsAntidiagonal.mp hp).2, ?_⟩
    rw [← he, pow_succ]
    exact Nat.mul_le_mul hi.2 (Finset.mem_Ioc.mp hmem).2

theorem detectorBlockCoefficients_pow_lower {N : ℕ} (hN : 0 < N)
    (T : ℝ) (j k n : ℕ) (hn : ((detectorBlockCoefficients T N j)^(k+1)) n ≠ 0) :
    N^(k+1) < n := by
  induction k generalizing n with
  | zero =>
    simp only [zero_add, pow_one] at hn ⊢
    have hmem : n ∈ Finset.Ioc N (2*N) := by
      by_contra h
      exact hn (by simp [detectorBlockCoefficients_apply, h])
    exact (Finset.mem_Ioc.mp hmem).1
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply] at hn
    obtain ⟨p, hp, hmul⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have ha := ih p.1 (left_ne_zero_of_mul hmul)
    have hb : detectorBlockCoefficients T N j p.2 ≠ 0 := right_ne_zero_of_mul hmul
    have hmem : p.2 ∈ Finset.Ioc N (2*N) := by
      by_contra h
      exact hb (by simp [detectorBlockCoefficients_apply, h])
    rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1, pow_succ]
    exact Nat.mul_lt_mul_of_pos_right ha hN |>.trans_le (Nat.mul_le_mul_left _ (Finset.mem_Ioc.mp hmem).1.le)

/-- Finite support, proved for the actual powers, gives absolute convergence. -/
theorem detectorBlockCoefficients_pow_LSeriesSummable (T : ℝ) (N j k : ℕ) (s : ℂ) :
    LSeriesSummable (fun n => ((detectorBlockCoefficients T N j)^k) n) s := by
  unfold LSeriesSummable
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Finset.range ((2*N)^k+1)).finite_toSet
  intro n hn
  apply Finset.mem_range.mpr
  by_contra h
  have hz : ((detectorBlockCoefficients T N j)^k) n = 0 := by
    by_contra hh
    have hi := detectorBlockCoefficients_pow_support T N j k n hh
    omega
  have ht : LSeries.term (fun n => ((detectorBlockCoefficients T N j)^k) n) s n = 0 := by
    rw [LSeries.term_def₀ ((detectorBlockCoefficients T N j)^k).map_zero]
    simp [hz]
  exact hn ht

/-- The finite L-series of the convolution power is the literal k-th power. -/
theorem detectorBlockCoefficients_LSeries_pow (T : ℝ) (N j k : ℕ) (s : ℂ) :
    LSeries (fun n => ((detectorBlockCoefficients T N j)^k) n) s =
      (LSeries (detectorBlockCoefficients T N j) s)^k := by
  induction k with
  | zero =>
    simp only [pow_zero]
    rw [LSeries, tsum_eq_single 1]
    · simp [ArithmeticFunction.one_apply]
    · intro n hn
      simp [LSeries.term_def, ArithmeticFunction.one_apply, hn]
  | succ k ih =>
    rw [pow_succ, ArithmeticFunction.LSeries_mul'
      (detectorBlockCoefficients_pow_LSeriesSummable T N j k s)
      (by simpa using detectorBlockCoefficients_pow_LSeriesSummable T N j 1 s), ih, pow_succ]

end MathCollab.Density
