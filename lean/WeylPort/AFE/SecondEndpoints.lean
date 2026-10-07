module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.SecondCoeffBounds

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Actual second-order Poisson endpoint simplifications -/

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory

/-- Conjugation changes the sign of the actual positive-tail endpoint. -/
theorem conj_positiveTail (x y : ℝ) : starRingEnd ℂ (positiveTail x y) = positiveTail (-x) y := by
  unfold positiveTail
  rw [Complex.conj_tsum]
  apply tsum_congr
  intro n
  split_ifs
  · rw [map_div₀, conj_expMode, Complex.conj_ofReal]
  · simp

/-- The positive-tail norm is unchanged when the endpoint is negated. -/
theorem norm_positiveTail_neg (x y : ℝ) : ‖positiveTail (-x) y‖ = ‖positiveTail x y‖ := by
  rw [← conj_positiveTail, Complex.norm_conj]

/-- The source H amplitude is nonnegative for all actual functions. -/
theorem secondH_nonneg (f g : ℝ → ℝ) (x : ℝ) : 0 ≤ secondH f g x := by
  unfold secondH
  positivity

/-- The source H₁ amplitude is nonnegative for all actual functions. -/
theorem secondH1_nonneg (f g : ℝ → ℝ) (x : ℝ) : 0 ≤ secondH1 f g x := by
  unfold secondH1
  positivity

/-- The literal half-integer B expression from Corollary 8.1 at N=0. -/
noncomputable def halfSecondEndpointBound (M : ℕ) (y : ℝ) : ℝ :=
  (1 / y) * (Real.pi / 2 + 1 / ((M : ℝ) + 1) + Real.log 2 + 3 / (2 * (y + 1)))

/-- Both actual oscillatory endpoint tails satisfy the complete half-integer source B bound. -/
theorem second_endpoint_half_integer_bound {M : ℕ} {x y : ℝ}
    (hx : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) (hy : 0 < y)
    (hδ : 1 / 2 ≤ (M : ℝ) + 1 - y) :
    ‖negativeTail M x y‖ + ‖positiveTail (-x) y‖ ≤ halfSecondEndpointBound M y := by
  rw [norm_positiveTail_neg]
  obtain ⟨k, rfl⟩ := hx
  have h := add_le_add (norm_negativeTail_half_integer_le_pi k hy hδ)
    (norm_positiveTail_half_integer_le k hy)
  apply h.trans_eq
  unfold halfSecondEndpointBound
  have hy1 : y + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The actual AFE finite Poisson estimate has the full half-integer boundary simplification, keeping the two square coefficients separate. -/
theorem afe_finite_poisson_second_half {σ c a b : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b)
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hbh : ∃ k : ℤ, b = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / a) :
    let f : ℝ → ℝ := afePhase c
    let g : ℝ → ℝ := afeWeight σ
    let M : ℕ := ⌊c / a⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M‖ ≤
      ((g a + g b) / (2 * Real.pi)) * (Real.log 2 + 1 / (c / a)) +
      secondH f g b / (4 * Real.pi ^ 2) * halfSecondEndpointBound M (c / b) +
      secondH f g a / (4 * Real.pi ^ 2) * halfSecondEndpointBound M (c / a) +
      secondH1 f g a / (4 * Real.pi ^ 3) *
        (minusSquareBound M (c / a) + plusSquareBound (c / a)) +
      (secondH f g a * (c / a ^ 2) / (4 * Real.pi ^ 3)) *
        (minusCubeBound M (c / a) + plusCubeBound (c / a)) := by
  dsimp only
  have hbpos := ha.trans hab
  have hya := div_pos hc ha
  have hyb := div_pos hc hbpos
  have hba : c / b ≤ c / a := div_le_div_of_nonneg_left hc.le ha hab.le
  have hδb : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / b := by linarith
  have heb := mul_le_mul_of_nonneg_left (second_endpoint_half_integer_bound hbh hyb hδb)
    (div_nonneg (secondH_nonneg (afePhase c) (afeWeight σ) b) (by positivity : 0 ≤ 4 * Real.pi ^ 2))
  have hea := mul_le_mul_of_nonneg_left (second_endpoint_half_integer_bound hah hya hδ)
    (div_nonneg (secondH_nonneg (afePhase c) (afeWeight σ) a) (by positivity : 0 ≤ 4 * Real.pi ^ 2))
  have hha := norm_poissonHeadBoundary_half_integer_le (f := afePhase c) hah (afeWeight_pos σ ha).le hya
  have hhb := norm_poissonHeadBoundary_half_integer_le (f := afePhase c) hbh (afeWeight_pos σ hbpos).le hya
  have hg : poissonBoundary (afePhase c) (afeWeight σ) a b = 0 := by
    obtain ⟨k, rfl⟩ := hah
    obtain ⟨l, rfl⟩ := hbh
    exact poissonBoundary_half_integer _ _ k l
  have ht := afe_finite_poisson_second_bound hσ hc ha hab
  dsimp only at ht
  rw [hg, norm_zero, add_zero] at ht
  simp only [div_eq_mul_inv] at ht hea heb hha hhb ⊢
  nlinarith only [ht, hea, heb, hha, hhb]

/-- The actual positive oscillatory tail has a uniform bound even at integer endpoints. -/
theorem norm_positiveTail_le_two {y : ℝ} (hy : 0 < y) (x : ℝ) : ‖positiveTail x y‖ ≤ 2 := by
  rw [positiveTail_eq_shift hy]
  have hs := reciprocal_square_series_bounds (by norm_num : (0 : ℝ) < 1)
  have hb : ‖∑' n : ℕ, (1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))) • expMode x (n + 1)‖ ≤
      ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
    apply tsum_of_norm_bounded hs.1.hasSum
    intro n
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))),
      norm_expMode, mul_one]
    apply one_div_le_one_div_of_le (by positivity : 0 < ((n : ℝ) + 1) ^ 2)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact hb.trans (by simpa only [one_pow, div_one, one_add_one_eq_two] using hs.2.2)

/-- At small positive derivative, the actual negative tail is uniformly bounded for every cutoff and endpoint. -/
theorem norm_negativeTail_le_four {M : ℕ} {y : ℝ} (hy : 0 < y) (hyhalf : y ≤ 1 / 2) (x : ℝ) :
    ‖negativeTail M x y‖ ≤ 4 := by
  have hM : y < (M : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  rw [negativeTail_eq_shift hy hM]
  have hs := reciprocal_square_series_bounds (by norm_num : (0 : ℝ) < 1)
  have hb : ‖∑' n : ℕ, (1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - y))) • expMode x (n + M + 1)‖ ≤
      2 * ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := by
    apply tsum_of_norm_bounded (hs.1.hasSum.mul_left 2)
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmn : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    have hgap : 0 < (n : ℝ) + M + 1 - y := by linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - y))),
      norm_expMode, mul_one]
    rw [mul_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hprod := mul_nonneg hmn (by positivity : 0 ≤ 2 * (n : ℝ) + M + 1)
    have hyprod := mul_nonneg (by positivity : 0 ≤ (n : ℝ) + M + 1) (show 0 ≤ 1 - 2 * y by linarith)
    nlinarith
  have hsum : (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2) ≤ 2 := by simpa only [one_pow, div_one, one_add_one_eq_two] using hs.2.2
  exact hb.trans (by linarith)

end DhimanKadiriQuesadaHerrera2026
