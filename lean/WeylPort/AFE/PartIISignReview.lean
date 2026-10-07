module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.AlternatingHarmonic

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # The printed Part-II E₁ does not bound its defining square-denominator tails

Source: frozen AFE2026ago31.tex, auxilliary_error1, compared with the two
preceding negative/positive square-tail estimates. The actual sum majorant
is proved here as a local correction to that coefficient.
-/

namespace DhimanKadiriQuesadaHerrera2026

/-- Literal E₁ from auxilliary_error1 in the frozen v1 source. -/
noncomputable def printedPartIIE1 (y : ℝ) : ℝ :=
  let δ : ℝ := 1 - (y - (⌊y⌋₊ : ℝ))
  1 / δ ^ 2 + 1 / (δ + 1) ^ 2 + 1 / (δ + 1) -
    1 / y * (Real.log ((⌊y⌋₊ : ℝ) + 1) - 1 / ((⌊y⌋₊ : ℝ) + 1) -
      (Complex.digamma (δ : ℂ)).re + Real.log (y + 1) + Real.eulerMascheroniConstant -
        (1 + 2 * y) / (2 * (1 + y)))

/-- The printed coefficient at the valid integer endpoint has an exact simple value. -/
theorem printedPartIIE1_one : printedPartIIE1 1 =
    3 - 2 * Real.log 2 - 2 * Real.eulerMascheroniConstant := by
  norm_num [printedPartIIE1, real_digamma_one]
  ring

/-- The coefficient is strictly below one, using rigorous logarithm and Euler-constant bounds. -/
theorem printedPartIIE1_one_lt_one : printedPartIIE1 1 < 1 := by
  have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≠ 1)
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
  rw [printedPartIIE1_one]
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- The actual two square-denominator tails that E₁ is intended to combine sum to exactly one. -/
theorem partII_square_tails_at_one :
    (∑' n : ℕ, 1 / (((n : ℝ) + 2) * ((n : ℝ) + 1) ^ 2)) +
      (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2)) = 1 := by
  have hn := (hasSum_harmonic_tail_square (N := 1) (y := 1)
    (by norm_num) (by norm_num)).tsum_eq
  have hp := (hasSum_harmonic_plus_square (y := 1) (by norm_num)).tsum_eq
  norm_num only [Nat.cast_one, add_sub_cancel_right, one_add_one_eq_two, one_pow, div_one,
    Complex.ofReal_one, Complex.ofReal_ofNat, real_digamma_one] at hn hp
  have hs := (reciprocal_square_series_bounds (by norm_num : (0 : ℝ) < 1)).1.tsum_eq_zero_add
  have hs' : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) =
      1 + ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 2 := by
    simpa only [Nat.cast_zero, zero_add, one_pow, div_one, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two] using hs
  norm_num only [add_assoc, one_add_one_eq_two] at hn hp
  linarith

/-- The literal printed E₁ is not a majorant of the very two tails used to derive it. -/
theorem printedPartIIE1_not_square_tail_bound :
    ¬ ((∑' n : ℕ, 1 / (((n : ℝ) + 2) * ((n : ℝ) + 1) ^ 2)) +
      (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 2)) ≤ printedPartIIE1 1) := by
  rw [partII_square_tails_at_one]
  exact not_le.mpr printedPartIIE1_one_lt_one


/-- The coefficient obtained by adding the two proved Lemma-1 bounds.
The majorant bounds the sum of the two square-denominator tails. -/
noncomputable def partIISquareTailEnvelope (y : ℝ) : ℝ :=
  let δ : ℝ := 1 - (y - (⌊y⌋₊ : ℝ))
  1 / δ ^ 2 + 1 / (δ + 1) ^ 2 + 1 / (δ + 1) -
    1 / y * (Real.log ((⌊y⌋₊ : ℝ) + 1) - 1 / ((⌊y⌋₊ : ℝ) + 1) -
      (Complex.digamma (δ : ℂ)).re - (Real.log (y + 1) + Real.eulerMascheroniConstant -
        (1 + 2 * y) / (2 * (1 + y))))

/-- Exact arithmetic identifies the sign discrepancy, without asserting the full Poisson estimate. -/
theorem partIISquareTailEnvelope_sub_printed (y : ℝ) :
    partIISquareTailEnvelope y - printedPartIIE1 y =
      2 / y * (Real.log (y + 1) + Real.eulerMascheroniConstant -
        (1 + 2 * y) / (2 * (1 + y))) := by
  unfold partIISquareTailEnvelope printedPartIIE1
  ring

/-- The corrected assembly is a genuine upper bound for both actual square-denominator tails. -/
theorem partII_square_tail_envelope_bound {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, 1 / (((n : ℝ) + ⌊y⌋₊ + 1) * ((n : ℝ) + ⌊y⌋₊ + 1 - y) ^ 2)) +
      (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ 2)) ≤
        partIISquareTailEnvelope y / y := by
  have h := add_le_add (harmonic_tail_square_bound hy (Nat.lt_floor_add_one y))
    (harmonic_plus_square_bound hy)
  rw [show (⌊y⌋₊ : ℝ) + 1 - y = 1 - (y - (⌊y⌋₊ : ℝ)) by ring] at h
  convert h using 1
  unfold partIISquareTailEnvelope
  dsimp only
  field_simp
  ring

/-- At y=1, the assembled majorant is exactly 3/2, while the actual combined tails equal one. -/
theorem partIISquareTailEnvelope_one : partIISquareTailEnvelope 1 = 3 / 2 := by
  norm_num [partIISquareTailEnvelope, real_digamma_one]
  ring

end DhimanKadiriQuesadaHerrera2026
