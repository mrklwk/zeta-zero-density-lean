module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.AlternatingHarmonic
public import Mathlib.Algebra.Field.GeomSum

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # The actual finite exponential sums of Lemma 2 -/

namespace DhimanKadiriQuesadaHerrera2026

open scoped BigOperators Topology

/-- The source's negative Fourier mode. -/
noncomputable def expMode (x : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((-2 * Real.pi * (n : ℝ) * x : ℝ) : ℂ))

/-- The exact positive-index finite sum S₀. -/
noncomputable def finiteS0 (x y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, expMode x n

/-- The exact twisted harmonic sum S₁. -/
noncomputable def finiteS1 (x y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, expMode x n / (n : ℂ)

/-- The generic piecewise majorant in the source display `bnd-Zxy`. -/
noncomputable def tildeS1 (x y : ℝ) : ℝ :=
  if 1 ≤ y then (1 / |Real.sin (Real.pi * x)|) * (1 / y + 1) else 0

/-- Reindexing preserves the first positive integer and the right endpoint. -/
theorem sum_Icc_one_eq_sum_range (f : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, f n) = ∑ n ∈ Finset.range N, f (n + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

/-- Every actual Fourier mode has unit norm. -/
theorem norm_expMode (x : ℝ) (n : ℕ) : ‖expMode x n‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

/-- The Fourier modes are the actual powers of their first mode. -/
theorem expMode_eq_pow (x : ℝ) (n : ℕ) : expMode x n = expMode x 1 ^ n := by
  unfold expMode
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The exact trigonometric size of a mode minus one. -/
theorem norm_expMode_sub_one (x : ℝ) (n : ℕ) :
    ‖expMode x n - 1‖ = 2 * |Real.sin (Real.pi * x * n)| := by
  unfold expMode
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,
    show (-2 * Real.pi * (n : ℝ) * x) / 2 = -(Real.pi * x * n) by ring,
    Real.sin_neg]
  simp [norm_mul, Real.norm_eq_abs]

/-- The denominator is nonzero whenever the source sine denominator is nonzero. -/
theorem expMode_one_ne_one {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) :
    expMode x 1 ≠ 1 := by
  intro h
  have he := norm_expMode_sub_one x 1
  rw [h, sub_self, norm_zero] at he
  norm_num at he
  exact hx he

/-- The exact sine quotient for every integer cutoff, including the empty sum. -/
theorem norm_finite_mode_sum {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, expMode x n‖ =
      |Real.sin (Real.pi * x * N)| / |Real.sin (Real.pi * x)| := by
  rw [sum_Icc_one_eq_sum_range]
  have hs : (∑ n ∈ Finset.range N, expMode x (n + 1)) =
      ∑ n ∈ Finset.range N, expMode x 1 ^ (n + 1) := by
    apply Finset.sum_congr rfl
    intro n _
    exact expMode_eq_pow x (n + 1)
  rw [hs]
  simp_rw [pow_succ]
  rw [← Finset.sum_mul, geom_sum_eq (expMode_one_ne_one hx), norm_mul,
    norm_expMode, mul_one, norm_div, ← expMode_eq_pow, norm_expMode_sub_one,
    norm_expMode_sub_one]
  simp only [Nat.cast_one, mul_one]
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- Lemma 2's exact geometric expression at a real cutoff. -/
theorem norm_finiteS0 {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) (y : ℝ) :
    ‖finiteS0 x y‖ = |Real.sin (Real.pi * x * ⌊y⌋₊)| / |Real.sin (Real.pi * x)| :=
  norm_finite_mode_sum hx _

/-- The uniform geometric bound used by the summation-by-parts step. -/
theorem norm_finiteS0_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) (y : ℝ) :
    ‖finiteS0 x y‖ ≤ 1 / |Real.sin (Real.pi * x)| := by
  rw [norm_finiteS0 hx]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)

/-- Finite summation by parts with nonnegative decreasing real weights. -/
theorem norm_weighted_sum_le {w : ℕ → ℝ} {z : ℕ → ℂ} {B : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w)
    (hB : ∀ N, ‖∑ n ∈ Finset.range N, z n‖ ≤ B) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w n • z n‖ ≤ w 0 * B := by
  have hB0 : 0 ≤ B := by simpa using hB 0
  cases N with
  | zero => simpa using mul_nonneg (hw 0) hB0
  | succ N =>
    rw [Finset.sum_range_by_parts, Nat.succ_sub_one]
    have hdiff (n : ℕ) : 0 ≤ w n - w (n + 1) := sub_nonneg.mpr (hanti (Nat.le_succ n))
    calc
      _ ≤ ‖w N • (∑ n ∈ Finset.range (N + 1), z n)‖ +
          ∑ n ∈ Finset.range N, ‖(w (n + 1) - w n) • (∑ j ∈ Finset.range (n + 1), z j)‖ := by
        exact (norm_sub_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
      _ = w N * ‖∑ n ∈ Finset.range (N + 1), z n‖ +
          ∑ n ∈ Finset.range N, (w n - w (n + 1)) * ‖∑ j ∈ Finset.range (n + 1), z j‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw N)]
        congr 1
        apply Finset.sum_congr rfl
        intro n _
        rw [norm_smul, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (hdiff n)]
      _ ≤ w N * B + ∑ n ∈ Finset.range N, (w n - w (n + 1)) * B := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hB _) (hw N)
        · apply Finset.sum_le_sum
          intro n _
          exact mul_le_mul_of_nonneg_left (hB _) (hdiff n)
      _ = w 0 * B := by
        rw [← Finset.sum_mul, Finset.sum_range_sub']
        ring

/-- The sharp finite Abel bound; it implies the looser printed S₁ estimate. -/
theorem norm_finiteS1_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) (y : ℝ) :
    ‖finiteS1 x y‖ ≤ 1 / |Real.sin (Real.pi * x)| := by
  have hanti : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    intro n m hnm
    apply one_div_le_one_div_of_le (by positivity)
    exact add_le_add_left (Nat.cast_le.mpr hnm) 1
  have hB (N : ℕ) : ‖∑ n ∈ Finset.range N, expMode x (n + 1)‖ ≤
      1 / |Real.sin (Real.pi * x)| := by
    rw [← sum_Icc_one_eq_sum_range, norm_finite_mode_sum hx]
    exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
  have h := norm_weighted_sum_le (w := fun n : ℕ => 1 / ((n : ℝ) + 1))
    (z := fun n => expMode x (n + 1)) (fun n => by positivity) hanti hB ⌊y⌋₊
  rw [finiteS1, sum_Icc_one_eq_sum_range]
  convert h using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro n _
    simp [Complex.real_smul, div_eq_mul_inv, mul_comm]
  · norm_num

/-- The exact printed noninteger S₁ bound for y at least one. -/
theorem norm_finiteS1_le_source {x y : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0) (hy : 1 ≤ y) :
    ‖finiteS1 x y‖ ≤ (1 / |Real.sin (Real.pi * x)|) * (1 / y + 1) := by
  have h := norm_finiteS1_le hx y
  have hB : 0 ≤ 1 / |Real.sin (Real.pi * x)| := by positivity
  have hy' : 0 ≤ 1 / y := by positivity
  nlinarith [mul_nonneg hB hy']

/-- Below the first positive integer, both source sums are empty. -/
theorem finite_sums_eq_zero {x y : ℝ} (hy : y < 1) : finiteS0 x y = 0 ∧ finiteS1 x y = 0 := by
  simp [finiteS0, finiteS1, Nat.floor_eq_zero.mpr hy]

/-- The paper's noninteger hypothesis discharges the sine denominator. -/
theorem sin_pi_mul_ne_zero_of_noninteger {x : ℝ} (hx : ∀ n : ℤ, x ≠ (n : ℝ)) :
    Real.sin (Real.pi * x) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.mp h
  have he : (n : ℝ) = x := by nlinarith [Real.pi_pos]
  exact hx n he.symm

/-- The actual mode at an integer frequency is one. -/
theorem expMode_integer (k : ℤ) (n : ℕ) : expMode (k : ℝ) n = 1 := by
  rw [expMode_eq_pow]
  have h : expMode (k : ℝ) 1 = 1 := by
    unfold expMode
    rw [show Complex.I * ((-2 * Real.pi * (1 : ℕ) * (k : ℝ) : ℝ) : ℂ) =
      ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
  rw [h, one_pow]

/-- At half-integers the actual modes have precisely the source's alternating signs. -/
theorem expMode_half_integer (k : ℤ) (n : ℕ) :
    expMode ((k : ℝ) + 1 / 2) n = (-1 : ℂ) ^ n := by
  rw [expMode_eq_pow]
  have h : expMode ((k : ℝ) + 1 / 2) 1 = -1 := by
    unfold expMode
    rw [show Complex.I * ((-2 * Real.pi * (1 : ℕ) * ((k : ℝ) + 1 / 2) : ℝ) : ℂ) =
      ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) + -(Real.pi * Complex.I) by
        push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
    simp [Complex.exp_neg, Complex.exp_pi_mul_I]
  rw [h]

/-- Integer frequencies return the exact number of included positive integers. -/
theorem finiteS0_integer (k : ℤ) (y : ℝ) : finiteS0 (k : ℝ) y = (⌊y⌋₊ : ℂ) := by
  simp [finiteS0, expMode_integer]

/-- Integer frequencies return the actual harmonic number. -/
theorem finiteS1_integer (k : ℤ) (y : ℝ) : finiteS1 (k : ℝ) y = (harmonic ⌊y⌋₊ : ℂ) := by
  rw [finiteS1, sum_Icc_one_eq_sum_range]
  simp only [expMode_integer, one_div, Nat.cast_add, Nat.cast_one]
  exact Complex.sum_inv_natCast_add_one _

private theorem antitone_reciprocal_succ : Antitone (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
  intro n m hnm
  apply one_div_le_one_div_of_le (by positivity)
  exact add_le_add_left (Nat.cast_le.mpr hnm) 1

private theorem sum_range_even_pairs (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range (2 * N), f n) = ∑ n ∈ Finset.range N, (f (2 * n) + f (2 * n + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

/-- The ordered alternating harmonic prefixes converge; no unordered reciprocal sum is used. -/
theorem tendsto_alternating_harmonic_prefix :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1)))
      Filter.atTop (𝓝 (Real.log 2)) := by
  have hlim : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) := by
    simpa only [one_div, Pi.inv_def] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1
        tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  obtain ⟨l, hl⟩ := antitone_reciprocal_succ.tendsto_alternating_series_of_tendsto_zero hlim
  have hp := hasSum_paired_reciprocal (by norm_num : (0 : ℝ) < 1)
  rw [paired_reciprocal_source_eq (by norm_num : (0 : ℝ) < 1)] at hp
  norm_num at hp
  have hfinite (N : ℕ) :
      (∑ n ∈ Finset.range (2 * N), (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) =
        ∑ n ∈ Finset.range N, (1 / (2 * (n : ℝ) + 1) - 1 / (2 * (n : ℝ) + 1 + 1)) := by
    rw [sum_range_even_pairs]
    apply Finset.sum_congr rfl
    intro n _
    norm_num [pow_add]
    ring
  have htwo : Filter.Tendsto (fun N : ℕ => 2 * N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => by dsimp; omega) Filter.tendsto_id
  have heven := hl.comp htwo
  simp only [Function.comp_def, hfinite] at heven
  simp only [one_div] at heven
  have he : l = Real.log 2 := tendsto_nhds_unique heven hp.tendsto_sum_nat
  rwa [he] at hl

/-- The alternating harmonic remainder is bounded by its first omitted reciprocal.
The parity argument specializes Mathlib's `alternating_series_error_bound` in
`Analysis/SpecificLimits/Normed.lean` (Apache-2.0), using an ordered limit instead
of unordered summability. Authors: Anatole Dedecker, Sébastien Gouëzel,
Yury Kudryashov, Dylan MacKenzie, Patrick Massot. -/
theorem alternating_harmonic_prefix_error (N : ℕ) :
    |(∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) - Real.log 2| ≤
      1 / ((N : ℝ) + 1) := by
  have hlow := Antitone.alternating_series_le_tendsto
    tendsto_alternating_harmonic_prefix antitone_reciprocal_succ
  have hupp := Antitone.tendsto_le_alternating_series
    tendsto_alternating_harmonic_prefix antitone_reciprocal_succ
  obtain he | ho := Nat.even_or_odd N
  · obtain ⟨k, rfl⟩ := even_iff_exists_two_mul.mp he
    have hl := hlow k
    have hu := hupp k
    simp only [Finset.sum_range_succ, even_two, Even.mul_right, Even.neg_pow,
      one_pow, one_mul] at hu
    rw [abs_sub_le_iff]
    have hp : 0 ≤ 1 / ((↑(2 * k) : ℝ) + 1) := by positivity
    constructor <;> linarith
  · obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp ho
    have hl := hlow (k + 1)
    have hu := hupp k
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, Finset.sum_range_succ] at hl
    norm_num [pow_add] at hl
    rw [abs_sub_le_iff]
    have hp : 0 ≤ 1 / ((↑(2 * k + 1) : ℝ) + 1) := by positivity
    simp only [one_div, Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hu hp ⊢
    constructor <;> linarith

/-- Exact conversion of the half-integer harmonic sum to a real alternating prefix. -/
theorem finiteS1_half_integer (k : ℤ) (y : ℝ) :
    finiteS1 ((k : ℝ) + 1 / 2) y =
      -((∑ n ∈ Finset.range ⌊y⌋₊, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1)) : ℝ) : ℂ) := by
  rw [finiteS1, sum_Icc_one_eq_sum_range]
  push_cast
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  rw [expMode_half_integer, pow_succ]
  ring

/-- The norm retains the absolute value of the actual alternating prefix. -/
theorem norm_finiteS1_half_integer (k : ℤ) (y : ℝ) :
    ‖finiteS1 ((k : ℝ) + 1 / 2) y‖ =
      |∑ n ∈ Finset.range ⌊y⌋₊, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))| := by
  rw [finiteS1_half_integer, norm_neg, Complex.norm_real, Real.norm_eq_abs]

/-- The half-integer refinement in Lemma 2, with its full two-sided O-star interpretation. -/
theorem finiteS1_half_integer_error (k : ℤ) {y : ℝ} (hy : 1 ≤ y) :
    |‖finiteS1 ((k : ℝ) + 1 / 2) y‖ - Real.log 2| ≤ 1 / y := by
  rw [norm_finiteS1_half_integer]
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hnorm :
      |(|∑ n ∈ Finset.range ⌊y⌋₊, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))|) - Real.log 2| ≤
        |(∑ n ∈ Finset.range ⌊y⌋₊, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) - Real.log 2| := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hlog] using
      abs_norm_sub_norm_le
        (∑ n ∈ Finset.range ⌊y⌋₊, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + 1))) (Real.log 2)
  refine (hnorm.trans (alternating_harmonic_prefix_error _)).trans ?_
  exact one_div_le_one_div_of_le (by linarith) (Nat.lt_floor_add_one y).le

/-- The corresponding half-integer upper bound used in the Poisson error. -/
theorem norm_finiteS1_half_integer_le (k : ℤ) {y : ℝ} (hy : 1 ≤ y) :
    ‖finiteS1 ((k : ℝ) + 1 / 2) y‖ ≤ Real.log 2 + 1 / y := by
  have h := (abs_le.mp (finiteS1_half_integer_error k hy)).2
  linarith

/-- The source's integer floor and the natural cutoff coincide in the positive domain. -/
theorem norm_finiteS0_source_floor {x y : ℝ} (hx : ∀ n : ℤ, x ≠ (n : ℝ)) (hy : 0 < y) :
    ‖finiteS0 x y‖ = |Real.sin (Real.pi * x * (⌊y⌋ : ℤ))| / |Real.sin (Real.pi * x)| := by
  rw [norm_finiteS0 (sin_pi_mul_ne_zero_of_noninteger hx),
    natCast_floor_eq_intCast_floor hy.le]

/-- Both branches of Lemma 2's geometric majorant, including the empty interval. -/
theorem norm_finiteS0_le_source {x y : ℝ} (hx : ∀ n : ℤ, x ≠ (n : ℝ)) :
    ‖finiteS0 x y‖ ≤ if 1 ≤ y then 1 / |Real.sin (Real.pi * x)| else 0 := by
  split_ifs with hy
  · exact norm_finiteS0_le (sin_pi_mul_ne_zero_of_noninteger hx) y
  · rw [(finite_sums_eq_zero (lt_of_not_ge hy)).1, norm_zero]

/-- The actual harmonic sum is bounded by the source's complete piecewise majorant. -/
theorem norm_finiteS1_le_tildeS1 {x y : ℝ} (hx : ∀ n : ℤ, x ≠ (n : ℝ)) :
    ‖finiteS1 x y‖ ≤ tildeS1 x y := by
  unfold tildeS1
  split_ifs with hy
  · exact norm_finiteS1_le_source (sin_pi_mul_ne_zero_of_noninteger hx) hy
  · rw [(finite_sums_eq_zero (lt_of_not_ge hy)).2, norm_zero]

/-- The prose bound preceding Lemma 2 fails already for a one-term half-integer sum. -/
theorem not_prose_log_bound :
    ¬ ‖finiteS1 (1 / 2) 1‖ ≤ Real.log (1 + |(1 : ℝ)|) := by
  have he : ‖finiteS1 (1 / 2) 1‖ = 1 := by
    simpa using norm_finiteS1_half_integer (0 : ℤ) (1 : ℝ)
  rw [he]
  norm_num
  have h : Real.log 2 < 1 := by
    convert Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num) using 1
    norm_num
  exact h

end DhimanKadiriQuesadaHerrera2026
