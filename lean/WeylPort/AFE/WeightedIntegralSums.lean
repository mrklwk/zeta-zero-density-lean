module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.FiniteExponentialSums

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # The finite arithmetic term in the weighted-integral estimate

The half-integer reciprocal sum is evaluated using the actual digamma recurrence.
The resulting bound preserves the correction 1/(8y²) in source Lemma 5.
-/

namespace DhimanKadiriQuesadaHerrera2026

open scoped BigOperators

/-- Extracted from AFEDigammaNumerics; no numerical certificates imported. -/
theorem real_digamma_add_nat {x : ℝ} (hx : 0 < x) (N : ℕ) :
    (Complex.digamma ((x + N : ℝ) : ℂ)).re = (Complex.digamma (x : ℂ)).re +
      ∑ n ∈ Finset.range N, 1 / (x + (n : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_add, Nat.cast_one, ← add_assoc,
      real_digamma_add_one (by positivity : 0 < x + (N : ℝ)), ih, Finset.sum_range_succ]
    ring



/-- The real-valued positive-index sum has the same precise endpoint convention. -/
theorem sum_Icc_one_eq_sum_range_real (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-- The positive-index arithmetic sum, in the real field used by the error bound. -/
theorem sum_Icc_natCast_real (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, (n : ℝ)) = (N : ℝ) * (N + 1) / 2 := by
  rw [sum_Icc_one_eq_sum_range_real]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Reflection of the finite index set identifies the half-integer reciprocal sum. -/
theorem half_integer_reciprocal_sum (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, 1 / ((N : ℝ) + 1 / 2 - m)) =
      (Complex.digamma (((N : ℝ) + 1 / 2 : ℝ) : ℂ)).re -
        (Complex.digamma (1 / 2 : ℂ)).re := by
  have hr : (∑ m ∈ Finset.Icc 1 N, 1 / ((N : ℝ) + 1 / 2 - m)) =
      ∑ n ∈ Finset.range N, 1 / (1 / 2 + (n : ℝ)) := by
    rw [sum_Icc_one_eq_sum_range_real,
      ← Finset.sum_range_reflect (fun n : ℕ => 1 / (1 / 2 + (n : ℝ))) N]
    apply Finset.sum_congr rfl
    intro n hn
    have hle : n + 1 ≤ N := Finset.mem_range.mp hn
    rw [show N - 1 - n = N - (n + 1) by omega, Nat.cast_sub hle, Nat.cast_add, Nat.cast_one]
    congr 1
    ring
  rw [hr, show (N : ℝ) + 1 / 2 = 1 / 2 + N by ring,
    real_digamma_add_nat (by norm_num : (0 : ℝ) < 1 / 2)]
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- Exact partial fractions retain both finite polynomial sums. -/
theorem half_integer_quadratic_sum_eq (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N,
      (m : ℝ) ^ 2 / (((N : ℝ) + 1 / 2) ^ 2 * ((N : ℝ) + 1 / 2 - m))) =
      (Complex.digamma (((N : ℝ) + 1 / 2 : ℝ) : ℂ)).re -
        (Complex.digamma (1 / 2 : ℂ)).re - (N : ℝ) / ((N : ℝ) + 1 / 2) -
          ((N : ℝ) * (N + 1) / 2) / ((N : ℝ) + 1 / 2) ^ 2 := by
  have he (m : ℕ) (hm : m ∈ Finset.Icc 1 N) :
      (m : ℝ) ^ 2 / (((N : ℝ) + 1 / 2) ^ 2 * ((N : ℝ) + 1 / 2 - m)) =
        1 / ((N : ℝ) + 1 / 2 - m) - 1 / ((N : ℝ) + 1 / 2) -
          (m : ℝ) / ((N : ℝ) + 1 / 2) ^ 2 := by
    have hmn : (m : ℝ) ≤ N := Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2
    have hy : 0 < (N : ℝ) + 1 / 2 := by positivity
    have hd : 0 < (N : ℝ) + 1 / 2 - m := by linarith
    generalize (N : ℝ) + 1 / 2 = y at hy hd ⊢
    field_simp
    ring
  rw [Finset.sum_congr rfl he, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    half_integer_reciprocal_sum, ← Finset.sum_div, ← Finset.sum_div, sum_Icc_natCast_real]
  simp

/-- The exact finite bound used in source Lemma 5, with its stated constant and correction. -/
theorem half_integer_quadratic_sum_le (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N,
      (m : ℝ) ^ 2 / (((N : ℝ) + 1 / 2) ^ 2 * ((N : ℝ) + 1 / 2 - m))) ≤
      Real.log ((N : ℝ) + 1 / 2) + Real.eulerMascheroniConstant + 2 * Real.log 2 -
        3 / 2 + 1 / (8 * ((N : ℝ) + 1 / 2) ^ 2) := by
  have hy : 0 < (N : ℝ) + 1 / 2 := by positivity
  have h := (real_digamma_bounds hy).2
  rw [half_integer_quadratic_sum_eq, real_digamma_half]
  calc
    _ ≤ Real.log ((N : ℝ) + 1 / 2) - 1 / (2 * ((N : ℝ) + 1 / 2)) +
        Real.eulerMascheroniConstant + 2 * Real.log 2 - (N : ℝ) / ((N : ℝ) + 1 / 2) -
          ((N : ℝ) * (N + 1) / 2) / ((N : ℝ) + 1 / 2) ^ 2 := by linarith
    _ = _ := by field_simp; ring

/-- The weighted alternating prefix has an exact closed form for either parity. -/
theorem alternating_linear_sum_eq (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m * (m : ℝ)) =
      ((-1 : ℝ) ^ N * (2 * (N : ℝ) + 1) - 1) / 4 := by
  rw [sum_Icc_one_eq_sum_range_real]
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

/-- The weighted alternating boundary term keeps the sharp half-size growth. -/
theorem abs_alternating_linear_sum_le (N : ℕ) :
    |∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m * (m : ℝ)| ≤ ((N : ℝ) + 1) / 2 := by
  rw [alternating_linear_sum_eq, abs_div]
  have h := abs_sub ((-1 : ℝ) ^ N * (2 * (N : ℝ) + 1)) 1
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (show 0 ≤ 2 * (N : ℝ) + 1 by positivity)] at h
  rw [show |(4 : ℝ)| = 4 by norm_num]
  linarith

/-- The same boundary estimate holds for the literal complex alternating sum. -/
theorem norm_alternating_linear_sum_le (N : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 N, (-1 : ℂ) ^ m * (m : ℂ)‖ ≤ ((N : ℝ) + 1) / 2 := by
  have he : (∑ m ∈ Finset.Icc 1 N, (-1 : ℂ) ^ m * (m : ℂ)) =
      ((∑ m ∈ Finset.Icc 1 N, (-1 : ℝ) ^ m * (m : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact abs_alternating_linear_sum_le N

/-- The unweighted complex alternating boundary sum is uniformly at most one. -/
theorem norm_alternating_sum_le_one (N : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 N, (-1 : ℂ) ^ m‖ ≤ 1 := by
  have hs : Real.sin (Real.pi * (1 / 2)) ≠ 0 := by
    rw [show Real.pi * (1 / 2) = Real.pi / 2 by ring, Real.sin_pi_div_two]
    norm_num
  have h := norm_finiteS0_le hs (N : ℝ)
  have hm (m : ℕ) : expMode (1 / 2) m = (-1 : ℂ) ^ m := by
    simpa only [Int.cast_zero, zero_add] using expMode_half_integer 0 m
  simpa only [finiteS0, Nat.floor_natCast, hm, show Real.pi * (1 / 2) = Real.pi / 2 by ring,
    Real.sin_pi_div_two, abs_one, div_one] using h

end DhimanKadiriQuesadaHerrera2026
