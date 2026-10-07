module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.WeightedIntegralPhase

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Assembly of the finite lower-integral estimate in Lemma 5

The actual J integrals are summed before estimating the two alternating endpoint
terms. The remaining weighted integrals use the proved physical-scale bound.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex
open scoped BigOperators

/-- The imaginary part controls both actual denominators in integration by parts. -/
theorem abs_height_le_norm_real_sub (a σ t : ℝ) :
    |t| ≤ ‖(a : ℂ) - ((σ : ℂ) + (t : ℂ) * I)‖ := by
  simpa only [sub_im, ofReal_im, add_im, mul_im, ofReal_re, I_im, I_re,
    mul_one, mul_zero, add_zero, zero_add, zero_sub, abs_neg] using
    abs_im_le_norm ((a : ℂ) - ((σ : ℂ) + (t : ℂ) * I))

/-- The product of the two integration-by-parts denominators retains the squared height. -/
theorem height_sq_le_norm_boundary_denominator (σ t : ℝ) :
    |t| ^ 2 ≤ ‖(1 - ((σ : ℂ) + (t : ℂ) * I)) * (2 - ((σ : ℂ) + (t : ℂ) * I))‖ := by
  rw [norm_mul, pow_two]
  simpa only [ofReal_one, ofReal_ofNat] using
    mul_le_mul (abs_height_le_norm_real_sub 1 σ t) (abs_height_le_norm_real_sub 2 σ t)
      (abs_nonneg t) (norm_nonneg _)

/-- Summing the exact two-step identity retains cancellation in both boundary sums. -/
theorem sum_weightedIntegral_parts_twice {s : ℂ} (hs : s.re < 1)
    {x : ℝ} (hx : 0 < x) (k : ℤ) (hxk : x = (k : ℝ) + 1 / 2) (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, weightedIntegral s 0 x (m : ℝ)) =
      ((x : ℂ) ^ (1 - s) / (1 - s)) * (∑ m ∈ Finset.Icc 1 N, (-1 : ℂ) ^ m) -
      ((2 * (Real.pi : ℂ) * I) * (x : ℂ) ^ (2 - s) / ((1 - s) * (2 - s))) *
        (∑ m ∈ Finset.Icc 1 N, (-1 : ℂ) ^ m * (m : ℂ)) -
      ((4 * (Real.pi : ℂ) ^ 2) / ((1 - s) * (2 - s))) *
        (∑ m ∈ Finset.Icc 1 N, (m : ℂ) ^ 2 * weightedIntegral (s - 2) 0 x (m : ℝ)) := by
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [weightedIntegral_parts_twice_half_integer hs hx k hxk m]
  ring

/-- The first exact boundary coefficient has its physical-height majorant. -/
theorem norm_lower_boundary_one_le {σ t x : ℝ} (hx : 0 < x) (ht : t ≠ 0) :
    ‖(x : ℂ) ^ (1 - ((σ : ℂ) + (t : ℂ) * I)) /
      (1 - ((σ : ℂ) + (t : ℂ) * I))‖ ≤ x ^ (1 - σ) / |t| := by
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos hx]
  have hr : (1 - ((σ : ℂ) + (t : ℂ) * I)).re = 1 - σ := by simp
  rw [hr]
  apply div_le_div_of_nonneg_left (Real.rpow_nonneg hx.le _) (abs_pos.mpr ht)
  simpa only [ofReal_one] using abs_height_le_norm_real_sub 1 σ t

/-- The second exact boundary coefficient has its squared-height majorant. -/
theorem norm_lower_boundary_two_le {σ t x : ℝ} (hx : 0 < x) (ht : t ≠ 0) :
    ‖((2 * (Real.pi : ℂ) * I) * (x : ℂ) ^ (2 - ((σ : ℂ) + (t : ℂ) * I))) /
      ((1 - ((σ : ℂ) + (t : ℂ) * I)) * (2 - ((σ : ℂ) + (t : ℂ) * I)))‖ ≤
      (2 * Real.pi * x ^ (2 - σ)) / |t| ^ 2 := by
  rw [norm_div, norm_mul, norm_mul, norm_mul, norm_ofNat, norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_cpow_eq_rpow_re_of_pos hx]
  have hr : (2 - ((σ : ℂ) + (t : ℂ) * I)).re = 2 - σ := by simp
  rw [hr]
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (abs_pos.mpr ht))
    (height_sq_le_norm_boundary_denominator σ t)

/-- The exact twice-integrated remainder coefficient has its squared-height majorant. -/
theorem norm_lower_remainder_coefficient_le {σ t : ℝ} (ht : t ≠ 0) :
    ‖(4 * (Real.pi : ℂ) ^ 2) /
      ((1 - ((σ : ℂ) + (t : ℂ) * I)) * (2 - ((σ : ℂ) + (t : ℂ) * I)))‖ ≤
      (4 * Real.pi ^ 2) / |t| ^ 2 := by
  rw [norm_div, norm_mul, norm_pow, norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos (abs_pos.mpr ht))
    (height_sq_le_norm_boundary_denominator σ t)

/-- The twice-integrated remainder sum is bounded using the linked source scale. -/
theorem norm_lower_remainder_sum_le {σ t x y : ℝ} (hσ : σ ≤ 2)
    (hx : 0 < x) (hy : 0 < y) (hscale : 2 * Real.pi * x * y = |t|)
    (N : ℕ) (hNy : (N : ℝ) < y) :
    ‖((4 * (Real.pi : ℂ) ^ 2) /
      ((1 - ((σ : ℂ) + (t : ℂ) * I)) * (2 - ((σ : ℂ) + (t : ℂ) * I)))) *
      (∑ m ∈ Finset.Icc 1 N, (m : ℂ) ^ 2 *
        weightedIntegral (((σ : ℂ) + (t : ℂ) * I) - 2) 0 x (m : ℝ))‖ ≤
      (x ^ (-σ) / Real.pi) * ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ 2 / (y ^ 2 * (y - m)) := by
  have ht : t ≠ 0 := by
    have hp : 0 < |t| := by rw [← hscale]; positivity
    exact (abs_pos.mp hp)
  have hp : x ^ (2 - σ) = x ^ 2 * x ^ (-σ) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx]
    congr 1
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m hm
  have hmy : (m : ℝ) < y := (Nat.cast_le.mpr (Finset.mem_Icc.mp hm).2).trans_lt hNy
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  calc
    _ ≤ (4 * Real.pi ^ 2 / |t| ^ 2) * ((m : ℝ) ^ 2 *
        (x ^ (2 - σ) / (Real.pi * (y - m)))) := by
      apply mul_le_mul (norm_lower_remainder_coefficient_le ht)
        (mul_le_mul_of_nonneg_left (norm_weightedIntegral_shift_two_source hσ
          (Nat.cast_nonneg m) hx hmy hscale) (sq_nonneg _)) (by positivity) (by positivity)
    _ = _ := by
      rw [← hscale, hp]
      field_simp
      ring

/-- The complete finite-integral sum is bounded before inserting the source's harmonic estimate. -/
theorem norm_sum_lower_integral_le_arithmetic {σ t x y : ℝ} (hσ : σ < 1)
    (hx : 0 < x) (hy : 0 < y) (hscale : 2 * Real.pi * x * y = |t|)
    (k : ℤ) (hxk : x = (k : ℝ) + 1 / 2) (N : ℕ) (hNy : (N : ℝ) < y) :
    ‖∑ m ∈ Finset.Icc 1 N, weightedIntegral ((σ : ℂ) + (t : ℂ) * I) 0 x (m : ℝ)‖ ≤
      x ^ (1 - σ) / |t| + (2 * Real.pi * x ^ (2 - σ) / |t| ^ 2) * (((N : ℝ) + 1) / 2) +
        (x ^ (-σ) / Real.pi) * ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ 2 / (y ^ 2 * (y - m)) := by
  have ht : t ≠ 0 := by
    have hp : 0 < |t| := by rw [← hscale]; positivity
    exact abs_pos.mp hp
  have hs : ((σ : ℂ) + (t : ℂ) * I).re < 1 := by simpa using hσ
  rw [sum_weightedIntegral_parts_twice hs hx k hxk N]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_sub_le (E := ℂ) _ _) (le_refl _)).trans ?_
  apply add_le_add _ (norm_lower_remainder_sum_le (by linarith) hx hy hscale N hNy)
  apply add_le_add
  · rw [norm_mul]
    have h := mul_le_mul (norm_lower_boundary_one_le (σ := σ) hx ht) (norm_alternating_sum_le_one N)
      (norm_nonneg _) (by positivity)
    simpa only [mul_one] using h
  · rw [norm_mul]
    exact mul_le_mul (norm_lower_boundary_two_le hx ht) (norm_alternating_linear_sum_le N)
      (norm_nonneg _) (by positivity)


/-- The full first estimate of Lemma 5, indexed by the exact half-integer cutoff. -/
theorem norm_sum_lower_integral_half_integer {σ t x y : ℝ} (hσ : σ < 1)
    (hx : 0 < x) (hscale : 2 * Real.pi * x * y = |t|)
    (k : ℤ) (hxk : x = (k : ℝ) + 1 / 2) (N : ℕ) (hyN : y = (N : ℝ) + 1 / 2) :
    ‖∑ m ∈ Finset.Icc 1 N, weightedIntegral ((σ : ℂ) + (t : ℂ) * I) 0 x (m : ℝ)‖ ≤
      x ^ (-σ) * (Real.log y / Real.pi +
        (Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2) / Real.pi +
          3 / (4 * Real.pi * y) + 3 / (8 * Real.pi * y ^ 2)) := by
  have hy : 0 < y := by rw [hyN]; positivity
  have hNy : (N : ℝ) < y := by rw [hyN]; linarith
  have hp₁ : x ^ (1 - σ) = x ^ (-σ) * x := by
    rw [show 1 - σ = -σ + 1 by ring, Real.rpow_add_one hx.ne']
  have hp₂ : x ^ (2 - σ) = x ^ 2 * x ^ (-σ) := by
    rw [← Real.rpow_natCast x 2, ← Real.rpow_add hx]
    congr 1
  have hb₁ : x ^ (1 - σ) / |t| = x ^ (-σ) / (2 * Real.pi * y) := by
    rw [← hscale, hp₁]
    field_simp
  have hb₂ : 2 * Real.pi * x ^ (2 - σ) / |t| ^ 2 * (((N : ℝ) + 1) / 2) =
      x ^ (-σ) * ((N : ℝ) + 1) / (4 * Real.pi * y ^ 2) := by
    rw [← hscale, hp₂]
    field_simp
    ring
  have hq := half_integer_quadratic_sum_le N
  rw [← hyN] at hq
  calc
    _ ≤ x ^ (1 - σ) / |t| +
        (2 * Real.pi * x ^ (2 - σ) / |t| ^ 2) * (((N : ℝ) + 1) / 2) +
        (x ^ (-σ) / Real.pi) * ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ 2 / (y ^ 2 * (y - m)) :=
      norm_sum_lower_integral_le_arithmetic hσ hx hy hscale k hxk N hNy
    _ ≤ x ^ (-σ) / (2 * Real.pi * y) +
        x ^ (-σ) * (y + 1) / (4 * Real.pi * y ^ 2) +
        (x ^ (-σ) / Real.pi) * (Real.log y + Real.eulerMascheroniConstant +
          2 * Real.log 2 - 3 / 2 + 1 / (8 * y ^ 2)) := by
      rw [hb₁, hb₂]
      apply add_le_add
      · apply add_le_add (le_refl _)
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith : (N : ℝ) + 1 ≤ y + 1)
            (Real.rpow_nonneg hx.le _)) (by positivity)
      · exact mul_le_mul_of_nonneg_left hq (by positivity)
    _ = _ := by field_simp; ring

/-- A positive half-integer has exactly its natural floor as the integer part. -/
theorem half_integer_eq_nat_floor_add_half {y : ℝ} (hy : 1 ≤ y)
    (k : ℤ) (hyk : y = (k : ℝ) + 1 / 2) : y = (⌊y⌋₊ : ℝ) + 1 / 2 := by
  have hk : 0 ≤ k := by
    have hr : (0 : ℝ) ≤ k := by linarith
    exact_mod_cast hr
  have he : (k.toNat : ℝ) = (k : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hk
  have hf : ⌊y⌋₊ = k.toNat := (Nat.floor_eq_iff (by linarith : 0 ≤ y)).mpr
    ⟨by rw [he]; linarith, by rw [he]; linarith⟩
  rw [hf, he, hyk]

/-- Lemma 5's complete finite lower-integral estimate at the literal real cutoff. -/
theorem norm_sum_lower_integral_source {σ t x y : ℝ} (hσ : σ < 1)
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hscale : 2 * Real.pi * x * y = |t|)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) :
    ‖∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegral ((σ : ℂ) + (t : ℂ) * I) 0 x (m : ℝ)‖ ≤
      x ^ (-σ) * (Real.log y / Real.pi +
        (Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2) / Real.pi +
          3 / (4 * Real.pi * y) + 3 / (8 * Real.pi * y ^ 2)) := by
  obtain ⟨k, hk⟩ := hxhalf
  obtain ⟨l, hl⟩ := hyhalf
  exact norm_sum_lower_integral_half_integer hσ (by linarith) hscale k hk ⌊y⌋₊
    (half_integer_eq_nat_floor_add_half hy l hl)

end DhimanKadiriQuesadaHerrera2026
