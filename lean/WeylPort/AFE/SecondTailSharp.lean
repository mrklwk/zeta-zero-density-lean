module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.SecondEndpoints

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Cancellation-preserving half-integer endpoint estimates -/

namespace DhimanKadiriQuesadaHerrera2026

/-- Keeping the paired reciprocal subtraction gives the sharp pi/(2y) tail bound. -/
theorem alternating_harmonic_tail_bound_sharp {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hδ : 1 / 2 ≤ (N : ℝ) + 1 - y) :
    |∑' n : ℕ, (-1 : ℝ) ^ n / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y))| ≤
      (Real.pi / 2) / y := by
  let d (u : ℝ) := ((Complex.digamma ((u + 1) / 2 : ℝ)).re -
    (Complex.digamma (u / 2 : ℝ)).re) / 2
  have hd : 0 < (N : ℝ) + 1 - y := by linarith
  have ha : 0 < (N : ℝ) + 1 := by positivity
  have hs : (∑' n : ℕ, (-1 : ℝ) ^ n /
      (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y))) =
      (d ((N : ℝ) + 1 - y) - d ((N : ℝ) + 1)) / y := by
    simpa only [d, show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring] using
      (hasSum_alternating_harmonic_tail hy (by linarith)).tsum_eq
  have hm : d ((N : ℝ) + 1) ≤ d ((N : ℝ) + 1 - y) :=
    paired_reciprocal_antitone hd (by linarith)
  have hn : 0 ≤ d ((N : ℝ) + 1) := (paired_reciprocal_bounds ha).1
  have hp : d ((N : ℝ) + 1 - y) ≤ Real.pi / 2 := by
    have hh := paired_reciprocal_antitone (by norm_num : (0 : ℝ) < 1 / 2) hδ
    have hv := paired_reciprocal_half
    norm_num at hh hv
    dsimp only [d]
    push_cast
    linarith
  rw [hs, abs_div, abs_of_pos hy, abs_of_nonneg (sub_nonneg.mpr hm)]
  exact div_le_div_of_nonneg_right (by linarith) hy.le

/-- The literal negative endpoint tail retains its alternating cancellation, including every initial sign. -/
theorem norm_negativeTail_half_integer_sharp {N : ℕ} (k : ℤ) {y : ℝ}
    (hy : 0 < y) (hδ : 1 / 2 ≤ (N : ℝ) + 1 - y) :
    ‖negativeTail N ((k : ℝ) + 1 / 2) y‖ ≤ (Real.pi / 2) / y := by
  rw [negativeTail_half_integer, Complex.norm_real, Real.norm_eq_abs]
  have hs : Summable (fun n : ℕ => (-1 : ℝ) ^ (n + N + 1) /
      ((↑(n + N + 1) : ℝ) * (↑(n + N + 1) - y))) := by
    have h := (hasSum_alternating_harmonic_tail hy (by linarith : y < (N : ℝ) + 1)).summable.mul_left
      ((-1 : ℝ) ^ (N + 1))
    convert h using 1
    funext n
    simp only [Nat.cast_add, Nat.cast_one, pow_add]
    ring
  rw [tsum_nat_tail_eq (F := fun ν : ℕ => (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) - y))) N hs]
  simp only [Nat.cast_add, Nat.cast_one]
  have he := abs_tsum_alternating_shift
    (fun n : ℕ => 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y))) (N + 1)
  simp only [← Nat.add_assoc, mul_one_div] at he
  rw [he]
  exact alternating_harmonic_tail_bound_sharp hy hδ

/-- The positive alternating tail is at most log(2)/y when its paired subtraction is retained. -/
theorem alternating_harmonic_plus_bound_sharp {y : ℝ} (hy : 0 < y) :
    |∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))| ≤
      Real.log 2 / y := by
  rw [(hasSum_alternating_harmonic_plus hy).tsum_eq, abs_div, abs_of_pos hy]
  have hn := (paired_reciprocal_bounds (by positivity : 0 < y + 1)).1
  have hm := paired_reciprocal_antitone (by norm_num : (0 : ℝ) < 1) (by linarith : 1 ≤ y + 1)
  norm_num only [one_add_one_eq_two, div_self (by norm_num : (2 : ℝ) ≠ 0), Complex.ofReal_one,
    Complex.ofReal_div, Complex.ofReal_ofNat] at hm
  rw [real_digamma_one, real_digamma_half] at hm
  rw [show y + 1 + 1 = y + 2 by ring] at hn hm
  push_cast at hn hm ⊢
  rw [abs_of_nonpos (by linarith)]
  apply div_le_div_of_nonneg_right _ hy.le
  linarith

/-- The actual positive endpoint tail satisfies log(2)/y at every half integer. -/
theorem norm_positiveTail_half_integer_sharp (k : ℤ) {y : ℝ} (hy : 0 < y) :
    ‖positiveTail ((k : ℝ) + 1 / 2) y‖ ≤ Real.log 2 / y := by
  rw [positiveTail_half_integer, Complex.norm_real, Real.norm_eq_abs]
  have hs : Summable (fun n : ℕ => (-1 : ℝ) ^ (n + 0 + 1) /
      ((↑(n + 0 + 1) : ℝ) * (↑(n + 0 + 1) + y))) := by
    simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one] using
      (hasSum_alternating_harmonic_plus hy).summable
  rw [tsum_nat_tail_eq (F := fun ν : ℕ => (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) + y))) 0 hs]
  simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one] using alternating_harmonic_plus_bound_sharp hy

/-- The two actual half-integer endpoint tails have a cancellation-preserving common bound. -/
theorem second_endpoint_half_integer_sharp {M : ℕ} {x y : ℝ}
    (hx : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) (hy : 0 < y)
    (hδ : 1 / 2 ≤ (M : ℝ) + 1 - y) :
    ‖negativeTail M x y‖ + ‖positiveTail (-x) y‖ ≤ (Real.pi / 2 + Real.log 2) / y := by
  rw [norm_positiveTail_neg]
  obtain ⟨k, rfl⟩ := hx
  simpa only [add_div] using add_le_add (norm_negativeTail_half_integer_sharp k hy hδ)
    (norm_positiveTail_half_integer_sharp k hy)

end DhimanKadiriQuesadaHerrera2026
