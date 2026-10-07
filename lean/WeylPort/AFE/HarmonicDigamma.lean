module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.Analytic.DigammaSeries
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Real digamma series and harmonic tails

Analytic inputs to Lemma 1. The complex digamma series is consumed from the
pinned PNT+ dependency; all inequalities here concern its actual real part.
-/

namespace DhimanKadiriQuesadaHerrera2026

open scoped BigOperators Topology
open Filter MeasureTheory

/-- The real series on the positive axis, with the original Euler constant. -/
theorem hasSum_real_digamma {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + x))
      ((Complex.digamma (x : ℂ)).re + Real.eulerMascheroniConstant) := by
  have hpoles : ∀ n : ℕ, (x : ℂ) ≠ -n := by
    intro n h
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  convert Complex.hasSum_re (Complex.hasSum_digamma hpoles) using 1
  · funext n
    have hcast : (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + x)) =
        ((1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + x) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hcast, Complex.ofReal_re]

/-- Difference of two digamma values as a convergent reciprocal-difference series. -/
theorem hasSum_digamma_difference {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + y))
      ((Complex.digamma (y : ℂ)).re - (Complex.digamma (x : ℂ)).re) := by
  convert (hasSum_real_digamma hy).sub (hasSum_real_digamma hx) using 1 <;>
    first | (funext n; ring) | ring

/-- The limiting logarithmic expression used in the integral comparisons. -/
theorem tendsto_log_sub_reciprocal_sum {x : ℝ} (hx : 0 < x) :
    Tendsto (fun N : ℕ => Real.log ((N : ℝ) + x) -
      ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + x)) atTop
        (𝓝 (Complex.digamma (x : ℂ)).re) := by
  have hs := (hasSum_real_digamma hx).tendsto_sum_nat
  have hl := (Real.tendsto_log_comp_add_sub_log x).comp tendsto_natCast_atTop_atTop
  have ht := (hs.sub Real.tendsto_harmonic_sub_log).add hl
  convert ht using 1
  · funext N
    rw [Finset.sum_sub_distrib]
    simp only [one_div, Complex.sum_inv_natCast_add_one_real, Function.comp_apply]
    ring
  · congr 1
    ring

/-- An exact tail identity, including the zero-frequency cutoff `N = 0`. -/
theorem hasSum_harmonic_tail {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y)))
      (((Complex.digamma ((N : ℝ) + 1 : ℝ)).re -
        (Complex.digamma ((N : ℝ) + 1 - y : ℝ)).re) / y) := by
  have hd : 0 < (N : ℝ) + 1 - y := by linarith
  have hs := (hasSum_digamma_difference hd (by positivity : 0 < (N : ℝ) + 1)).div_const y
  convert hs using 1
  funext n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (n : ℝ) + ((N : ℝ) + 1 - y) ≠ 0 := by positivity
  have h2 : (n : ℝ) + ((N : ℝ) + 1) ≠ 0 := by positivity
  have h3 : (n : ℝ) + N + 1 - y ≠ 0 := by linarith
  have h4 : (n : ℝ) + N + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The reciprocal function lies below its chord on a positive unit interval. -/
theorem reciprocal_le_chord {u t : ℝ} (hu : 0 < u) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    1 / (u + t) ≤ (1 - t) / u + t / (u + 1) := by
  have ht0 := ht.1
  have ht1 := ht.2
  have hut : 0 < u + t := by positivity
  have hu1 : 0 < u + 1 := by positivity
  field_simp
  nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]

/-- Trapezoidal upper bound for the logarithm on a positive unit interval. -/
theorem log_succ_sub_le {u : ℝ} (hu : 0 < u) :
    Real.log (u + 1) - Real.log u ≤ (1 / u + 1 / (u + 1)) / 2 := by
  have hrec : IntervalIntegrable (fun t : ℝ => 1 / (u + t)) volume 0 1 := by
    apply intervalIntegral.intervalIntegrable_one_div
    · intro t ht
      rw [Set.uIcc_of_le (by norm_num)] at ht
      exact (add_pos_of_pos_of_nonneg hu ht.1).ne'
    · fun_prop
  have hchord : Continuous (fun t : ℝ => (1 - t) / u + t / (u + 1)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    hrec (hchord.intervalIntegrable 0 1) (fun t ht => reciprocal_le_chord hu ht)
  have hl : (∫ t : ℝ in (0 : ℝ)..1, 1 / (u + t)) =
      Real.log (u + 1) - Real.log u := by
    rw [intervalIntegral.integral_comp_add_left (fun v : ℝ => 1 / v) u]
    simp only [add_zero]
    rw [integral_one_div_of_pos hu (by positivity),
      Real.log_div (by positivity) hu.ne']
  have hc : (∫ t : ℝ in (0 : ℝ)..1, (1 - t) / u + t / (u + 1)) =
      (1 / u + 1 / (u + 1)) / 2 := by
    have hleft : IntervalIntegrable (fun t : ℝ => (1 - t) / u) volume 0 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hright : IntervalIntegrable (fun t : ℝ => t / (u + 1)) volume 0 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_add hleft hright,
      intervalIntegral.integral_div, intervalIntegral.integral_div,
      intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x)
        intervalIntegrable_const (show IntervalIntegrable (fun x : ℝ => x) volume 0 1 from
          continuous_id.intervalIntegrable 0 1),
      intervalIntegral.integral_const, integral_id]
    norm_num
    ring
  rwa [hl, hc] at hi

/-- Rectangular lower bound for the logarithm on a positive unit interval. -/
theorem le_log_succ_sub {u : ℝ} (hu : 0 < u) :
    1 / (u + 1) ≤ Real.log (u + 1) - Real.log u := by
  have h := Real.log_le_sub_one_of_pos (div_pos hu (by positivity : 0 < u + 1))
  rw [Real.log_div hu.ne' (by positivity)] at h
  have he : u / (u + 1) - 1 = -(1 / (u + 1)) := by field_simp; ring
  rw [he] at h
  linarith

/-- Finite integral-comparison bounds, retaining both endpoint corrections. -/
theorem log_sub_reciprocal_sum_bounds {x : ℝ} (hx : 0 < x) (N : ℕ) :
    Real.log x - 1 / x + 1 / ((N : ℝ) + x) ≤
        Real.log ((N : ℝ) + x) - ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + x) ∧
      Real.log ((N : ℝ) + x) - ∑ n ∈ Finset.range N, 1 / ((n : ℝ) + x) ≤
        Real.log x - (1 / x) / 2 + (1 / ((N : ℝ) + x)) / 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hu : 0 < (N : ℝ) + x := by positivity
    have hlo := le_log_succ_sub hu
    have hhi := log_succ_sub_le hu
    rw [Finset.sum_range_succ]
    push_cast
    rw [show (N : ℝ) + 1 + x = (N : ℝ) + x + 1 by ring]
    constructor <;> linarith [ih.1, ih.2]

/-- The precise elementary digamma bounds used in Lemma 1. -/
theorem real_digamma_bounds {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / x ≤ (Complex.digamma (x : ℂ)).re ∧
      (Complex.digamma (x : ℂ)).re ≤ Real.log x - 1 / (2 * x) := by
  have hlim := tendsto_log_sub_reciprocal_sum hx
  have hinv : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + x)) atTop (𝓝 0) := by
    simpa only [one_div, Pi.inv_def] using
      (tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  constructor
  · apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    apply Eventually.of_forall
    intro N
    have h := (log_sub_reciprocal_sum_bounds hx N).1
    have hpos : 0 ≤ 1 / ((N : ℝ) + x) := by positivity
    linarith
  · have hlim' := hlim.sub (hinv.div_const 2)
    have h : (Complex.digamma (x : ℂ)).re - 0 / 2 ≤ Real.log x - (1 / x) / 2 := by
      apply le_of_tendsto hlim'
      apply Eventually.of_forall
      intro N
      linarith [(log_sub_reciprocal_sum_bounds hx N).2]
    convert h using 1 <;> ring

/-- The full two-sided first harmonic-tail estimate in Lemma 1, also valid at `N = 0`. -/
theorem harmonic_tail_bounds {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) :
    -1 / (y * ((N : ℝ) + 1)) - (Complex.digamma ((N : ℝ) + 1 - y : ℝ)).re / y ≤
        (∑' n : ℕ, 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y))) -
          Real.log ((N : ℝ) + 1) / y ∧
      (∑' n : ℕ, 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y))) -
          Real.log ((N : ℝ) + 1) / y ≤
        -1 / (2 * y * ((N : ℝ) + 1)) -
          (Complex.digamma ((N : ℝ) + 1 - y : ℝ)).re / y := by
  rw [(hasSum_harmonic_tail hy hNy).tsum_eq]
  have hb := real_digamma_bounds (by positivity : 0 < (N : ℝ) + 1)
  have hlo := div_le_div_of_nonneg_right hb.1 hy.le
  have hhi := div_le_div_of_nonneg_right hb.2 hy.le
  constructor
  · convert sub_le_sub_right hlo
      ((Complex.digamma ((N : ℝ) + 1 - y : ℝ)).re / y +
        Real.log ((N : ℝ) + 1) / y) using 1 <;>
      simp only [div_eq_mul_inv, mul_inv_rev] <;> ring
  · convert sub_le_sub_right hhi
      ((Complex.digamma ((N : ℝ) + 1 - y : ℝ)).re / y +
        Real.log ((N : ℝ) + 1) / y) using 1 <;>
      simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

/-- Exact positive-shift counterpart of the first harmonic-tail identity. -/
theorem hasSum_harmonic_plus {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y)))
      (((Complex.digamma (y + 1 : ℝ)).re + Real.eulerMascheroniConstant) / y) := by
  have hs := (hasSum_real_digamma (by positivity : 0 < y + 1)).div_const y
  convert hs using 1
  funext n
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + (y + 1) ≠ 0 := by positivity
  have h3 : (n : ℝ) + 1 + y ≠ 0 := by positivity
  field_simp
  ring

/-- The positive-shift estimate of Lemma 1 for the first power. -/
theorem harmonic_plus_bound {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))) ≤
      (Real.log (y + 1) + Real.eulerMascheroniConstant) / y - 1 / (2 * y * (y + 1)) := by
  rw [(hasSum_harmonic_plus hy).tsum_eq]
  have h := div_le_div_of_nonneg_right
    (add_le_add_right (real_digamma_bounds (by positivity : 0 < y + 1)).2
      Real.eulerMascheroniConstant) hy.le
  convert h using 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

private theorem sum_bounds_from_differences (f F : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hF : Tendsto F atTop (𝓝 0))
    (hlo : ∀ n, F n - F (n + 1) ≤ f n)
    (hhi : ∀ n, f (n + 1) ≤ F n - F (n + 1)) :
    Summable f ∧ F 0 ≤ ∑' n, f n ∧ (∑' n, f n) ≤ f 0 + F 0 := by
  have hd : HasSum (fun n => F n - F (n + 1)) (F 0) := by
    apply (hasSum_iff_tendsto_nat_of_nonneg (fun n => (hf (n + 1)).trans (hhi n)) _).mpr
    simpa only [Finset.sum_range_sub', sub_zero] using tendsto_const_nhds.sub hF
  have ht : Summable (fun n => f (n + 1)) :=
    Summable.of_nonneg_of_le (fun n => hf (n + 1)) hhi hd.summable
  have hs : Summable f := (summable_nat_add_iff 1).mp ht
  refine ⟨hs, ?_, ?_⟩
  · rw [← hd.tsum_eq]
    exact hd.summable.tsum_le_tsum hlo hs
  · rw [hs.tsum_eq_zero_add, ← hd.tsum_eq]
    exact add_le_add_right (ht.tsum_le_tsum hhi hd.summable) _

/-- Convergence and integral bounds for reciprocal squares on any positive translate. -/
theorem reciprocal_square_series_bounds {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + x) ^ 2) ∧
      1 / x ≤ ∑' n : ℕ, 1 / ((n : ℝ) + x) ^ 2 ∧
      (∑' n : ℕ, 1 / ((n : ℝ) + x) ^ 2) ≤ 1 / x ^ 2 + 1 / x := by
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + x)) atTop (𝓝 0) := by
    simpa only [one_div, Pi.inv_def] using
      (tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have h := sum_bounds_from_differences (fun n : ℕ => 1 / ((n : ℝ) + x) ^ 2)
    (fun n : ℕ => 1 / ((n : ℝ) + x)) (fun n => by positivity) hlim
  simp only [Nat.cast_zero, zero_add] at h
  apply h
  · intro n
    have hu : 0 < (n : ℝ) + x := by positivity
    have hu1 : 0 < (n : ℝ) + x + 1 := by positivity
    push_cast
    rw [show (n : ℝ) + 1 + x = (n : ℝ) + x + 1 by ring]
    field_simp
    nlinarith
  · intro n
    have hu : 0 < (n : ℝ) + x := by positivity
    have hu1 : 0 < (n : ℝ) + x + 1 := by positivity
    push_cast
    rw [show (n : ℝ) + 1 + x = (n : ℝ) + x + 1 by ring]
    field_simp
    nlinarith

/-- Convergence and integral bounds for reciprocal cubes on any positive translate. -/
theorem reciprocal_cube_series_bounds {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + x) ^ 3) ∧
      1 / (2 * x ^ 2) ≤ ∑' n : ℕ, 1 / ((n : ℝ) + x) ^ 3 ∧
      (∑' n : ℕ, 1 / ((n : ℝ) + x) ^ 3) ≤ 1 / x ^ 3 + 1 / (2 * x ^ 2) := by
  have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + x)) atTop (𝓝 0) := by
    simpa only [one_div, Pi.inv_def] using
      (tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hlim : Tendsto (fun n : ℕ => 1 / (2 * ((n : ℝ) + x) ^ 2)) atTop (𝓝 0) := by
    convert (hinv.pow 2).div_const 2 using 1
    · funext n
      simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
      ring
    · norm_num
  have h := sum_bounds_from_differences (fun n : ℕ => 1 / ((n : ℝ) + x) ^ 3)
    (fun n : ℕ => 1 / (2 * ((n : ℝ) + x) ^ 2)) (fun n => by positivity) hlim
  simp only [Nat.cast_zero, zero_add] at h
  apply h
  · intro n
    have hu : 0 < (n : ℝ) + x := by positivity
    have hu1 : 0 < (n : ℝ) + x + 1 := by positivity
    push_cast
    rw [show (n : ℝ) + 1 + x = (n : ℝ) + x + 1 by ring]
    field_simp
    nlinarith [sq_pos_of_pos hu, pow_pos hu 3]
  · intro n
    have hu : 0 < (n : ℝ) + x := by positivity
    have hu1 : 0 < (n : ℝ) + x + 1 := by positivity
    push_cast
    rw [show (n : ℝ) + 1 + x = (n : ℝ) + x + 1 by ring]
    field_simp
    nlinarith [sq_pos_of_pos hu, pow_pos hu 3]

/-- The sharpened reciprocal-square bounds after retaining the first term. -/
theorem reciprocal_square_series_sharp {x : ℝ} (hx : 0 < x) :
    1 / x ^ 2 + 1 / (x + 1) ≤ ∑' n : ℕ, 1 / ((n : ℝ) + x) ^ 2 ∧
      (∑' n : ℕ, 1 / ((n : ℝ) + x) ^ 2) ≤
        1 / x ^ 2 + 1 / (x + 1) ^ 2 + 1 / (x + 1) := by
  have he : (∑' n : ℕ, 1 / ((n : ℝ) + x) ^ 2) =
      1 / x ^ 2 + ∑' n : ℕ, 1 / ((n : ℝ) + (x + 1)) ^ 2 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, add_assoc,
      add_comm 1 x] using (reciprocal_square_series_bounds hx).1.tsum_eq_zero_add
  rw [he]
  have h := (reciprocal_square_series_bounds (by positivity : 0 < x + 1)).2
  constructor <;> linarith [h.1, h.2]

/-- The sharpened reciprocal-cube bounds after retaining the first term. -/
theorem reciprocal_cube_series_sharp {x : ℝ} (hx : 0 < x) :
    1 / x ^ 3 + 1 / (2 * (x + 1) ^ 2) ≤ ∑' n : ℕ, 1 / ((n : ℝ) + x) ^ 3 ∧
      (∑' n : ℕ, 1 / ((n : ℝ) + x) ^ 3) ≤
        1 / x ^ 3 + 1 / (x + 1) ^ 3 + 1 / (2 * (x + 1) ^ 2) := by
  have he : (∑' n : ℕ, 1 / ((n : ℝ) + x) ^ 3) =
      1 / x ^ 3 + ∑' n : ℕ, 1 / ((n : ℝ) + (x + 1)) ^ 3 := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_add, add_assoc,
      add_comm 1 x] using (reciprocal_cube_series_bounds hx).1.tsum_eq_zero_add
  rw [he]
  have h := (reciprocal_cube_series_bounds (by positivity : 0 < x + 1)).2
  constructor <;> linarith [h.1, h.2]

/-- Convergent partial-fraction decomposition for the second negative-shift power. -/
theorem hasSum_harmonic_tail_square {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y) ^ 2))
      ((∑' n : ℕ, 1 / ((n : ℝ) + ((N : ℝ) + 1 - y)) ^ 2) / y -
        ((Complex.digamma ((N : ℝ) + 1 : ℝ)).re -
          (Complex.digamma ((N : ℝ) + 1 - y : ℝ)).re) / y ^ 2) := by
  have hd : 0 < (N : ℝ) + 1 - y := by linarith
  have h := ((reciprocal_square_series_bounds hd).1.hasSum.div_const y).sub
    ((hasSum_harmonic_tail hy hNy).div_const y)
  convert h using 1
  · funext n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : (n : ℝ) + N + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + N + 1 - y ≠ 0 := by linarith
    have h3 : (n : ℝ) + ((N : ℝ) + 1 - y) ≠ 0 := by positivity
    field_simp
    ring
  · ring

/-- Convergent partial-fraction decomposition for the third negative-shift power. -/
theorem hasSum_harmonic_tail_cube {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y) ^ 3))
      ((∑' n : ℕ, 1 / ((n : ℝ) + ((N : ℝ) + 1 - y)) ^ 3) / y -
        (∑' n : ℕ, 1 / ((n : ℝ) + ((N : ℝ) + 1 - y)) ^ 2) / y ^ 2 +
        ((Complex.digamma ((N : ℝ) + 1 : ℝ)).re -
          (Complex.digamma ((N : ℝ) + 1 - y : ℝ)).re) / y ^ 3) := by
  have hd : 0 < (N : ℝ) + 1 - y := by linarith
  have h := (((reciprocal_cube_series_bounds hd).1.hasSum.div_const y).sub
    ((reciprocal_square_series_bounds hd).1.hasSum.div_const (y ^ 2))).add
    ((hasSum_harmonic_tail hy hNy).div_const (y ^ 2))
  convert h using 1
  · funext n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : (n : ℝ) + N + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + N + 1 - y ≠ 0 := by linarith
    have h3 : (n : ℝ) + ((N : ℝ) + 1 - y) ≠ 0 := by positivity
    field_simp
    ring
  · ring

/-- The complete second negative-shift estimate of Lemma 1. -/
theorem harmonic_tail_square_bound {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) :
    let δ : ℝ := (N : ℝ) + 1 - y
    (∑' n : ℕ, 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y) ^ 2)) ≤
      (1 / δ ^ 2 + 1 / (δ + 1) ^ 2 + 1 / (δ + 1)) / y -
        (Real.log ((N : ℝ) + 1) - 1 / ((N : ℝ) + 1) -
          (Complex.digamma (δ : ℂ)).re) / y ^ 2 := by
  dsimp only
  rw [(hasSum_harmonic_tail_square hy hNy).tsum_eq]
  have hd : 0 < (N : ℝ) + 1 - y := by linarith
  exact sub_le_sub
    (div_le_div_of_nonneg_right (reciprocal_square_series_sharp hd).2 hy.le)
    (div_le_div_of_nonneg_right
      (sub_le_sub_right (real_digamma_bounds (by positivity : 0 < (N : ℝ) + 1)).1 _)
      (sq_nonneg y))

/-- The complete third negative-shift estimate of Lemma 1. -/
theorem harmonic_tail_cube_bound {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) :
    let δ : ℝ := (N : ℝ) + 1 - y
    (∑' n : ℕ, 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y) ^ 3)) ≤
      (1 / δ ^ 3 + 1 / (δ + 1) ^ 3 + 1 / (2 * (δ + 1) ^ 2)) / y -
        (1 / δ ^ 2 + 1 / (δ + 1)) / y ^ 2 +
        (Real.log ((N : ℝ) + 1) - 1 / (2 * ((N : ℝ) + 1)) -
          (Complex.digamma (δ : ℂ)).re) / y ^ 3 := by
  dsimp only
  rw [(hasSum_harmonic_tail_cube hy hNy).tsum_eq]
  have hd : 0 < (N : ℝ) + 1 - y := by linarith
  exact add_le_add
    (sub_le_sub
      (div_le_div_of_nonneg_right (reciprocal_cube_series_sharp hd).2 hy.le)
      (div_le_div_of_nonneg_right (reciprocal_square_series_sharp hd).1 (sq_nonneg y)))
    (div_le_div_of_nonneg_right
      (sub_le_sub_right (real_digamma_bounds (by positivity : 0 < (N : ℝ) + 1)).2 _)
      (by positivity))

/-- Convergent partial fractions for the second positive-shift power. -/
theorem hasSum_harmonic_plus_square {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ 2))
      (((Complex.digamma (y + 1 : ℝ)).re + Real.eulerMascheroniConstant) / y ^ 2 -
        (∑' n : ℕ, 1 / ((n : ℝ) + (y + 1)) ^ 2) / y) := by
  have h := ((hasSum_harmonic_plus hy).div_const y).sub
    ((reciprocal_square_series_bounds (by positivity : 0 < y + 1)).1.hasSum.div_const y)
  convert h using 1
  · funext n
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 + y ≠ 0 := by positivity
    have h3 : (n : ℝ) + (y + 1) ≠ 0 := by positivity
    field_simp
    ring
  · ring

/-- Convergent partial fractions for the third positive-shift power. -/
theorem hasSum_harmonic_plus_cube {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ 3))
      (((Complex.digamma (y + 1 : ℝ)).re + Real.eulerMascheroniConstant) / y ^ 3 -
        (∑' n : ℕ, 1 / ((n : ℝ) + (y + 1)) ^ 2) / y ^ 2 -
        (∑' n : ℕ, 1 / ((n : ℝ) + (y + 1)) ^ 3) / y) := by
  have h := (((hasSum_harmonic_plus hy).div_const (y ^ 2)).sub
    ((reciprocal_square_series_bounds (by positivity : 0 < y + 1)).1.hasSum.div_const
      (y ^ 2))).sub
    ((reciprocal_cube_series_bounds (by positivity : 0 < y + 1)).1.hasSum.div_const y)
  convert h using 1
  · funext n
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 + y ≠ 0 := by positivity
    have h3 : (n : ℝ) + (y + 1) ≠ 0 := by positivity
    field_simp
    ring
  · ring

/-- The positive-shift estimate of Lemma 1 for the second power. -/
theorem harmonic_plus_square_bound {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ 2)) ≤
      (Real.log (y + 1) + Real.eulerMascheroniConstant) / y ^ 2 -
        (1 + 2 * y) / (2 * y ^ 2 * (y + 1)) := by
  rw [(hasSum_harmonic_plus_square hy).tsum_eq]
  have h := sub_le_sub
    (div_le_div_of_nonneg_right
      (add_le_add_right (real_digamma_bounds (by positivity : 0 < y + 1)).2
        Real.eulerMascheroniConstant) (sq_nonneg y))
    (div_le_div_of_nonneg_right
      (reciprocal_square_series_bounds (by positivity : 0 < y + 1)).2.1 hy.le)
  convert h using 1 <;> field_simp <;> ring

/-- The positive-shift estimate of Lemma 1 for the third power. -/
theorem harmonic_plus_cube_bound {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ 3)) ≤
      (Real.log (y + 1) + Real.eulerMascheroniConstant) / y ^ 3 -
        (1 + 3 * y + 3 * y ^ 2) / (2 * y ^ 3 * (y + 1) ^ 2) := by
  rw [(hasSum_harmonic_plus_cube hy).tsum_eq]
  have h := sub_le_sub
    (sub_le_sub
      (div_le_div_of_nonneg_right
        (add_le_add_right (real_digamma_bounds (by positivity : 0 < y + 1)).2
          Real.eulerMascheroniConstant) (by positivity : 0 ≤ y ^ 3))
      (div_le_div_of_nonneg_right
        (reciprocal_square_series_bounds (by positivity : 0 < y + 1)).2.1 (sq_nonneg y)))
    (div_le_div_of_nonneg_right
      (reciprocal_cube_series_bounds (by positivity : 0 < y + 1)).2.1 hy.le)
  convert h using 1 <;> field_simp <;> ring

/-- Reindex an actual natural-number tail by its first included integer. -/
theorem tsum_nat_tail_eq {F : ℕ → ℝ} (N : ℕ)
    (hF : Summable (fun n : ℕ => F (n + N + 1))) :
    (∑' ν : ℕ, if N < ν then F ν else 0) = ∑' n : ℕ, F (n + N + 1) := by
  let f : ℕ → ℝ := fun ν => if N < ν then F ν else 0
  have htail : (fun n => f (n + (N + 1))) = (fun n => F (n + N + 1)) := by
    funext n
    simp only [f, show N < n + (N + 1) by omega, ite_true, Nat.add_assoc]
  have hs : Summable f := (summable_nat_add_iff (N + 1)).mp (htail.symm ▸ hF)
  have hhead : ∑ ν ∈ Finset.range (N + 1), f ν = 0 := by
    apply Finset.sum_eq_zero
    intro ν hν
    simp only [Finset.mem_range] at hν
    simp only [f, show ¬ N < ν by omega, ite_false]
  have he := hs.sum_add_tsum_nat_add (N + 1)
  rw [hhead, zero_add, htail] at he
  exact he.symm

/-- Source-index form of the harmonic-tail identity, with the exact `ν > N` condition. -/
theorem source_harmonic_tail_identity {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) :
    (∑' ν : ℕ, if N < ν then 1 / ((ν : ℝ) * ((ν : ℝ) - y)) else 0) =
      ((Complex.digamma ((N : ℝ) + 1 : ℝ)).re -
        (Complex.digamma ((N : ℝ) + 1 - y : ℝ)).re) / y := by
  have hs : Summable (fun n : ℕ => 1 / ((↑(n + N + 1) : ℝ) * (↑(n + N + 1) - y))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (hasSum_harmonic_tail hy hNy).summable
  rw [tsum_nat_tail_eq (F := fun ν : ℕ => 1 / ((ν : ℝ) * ((ν : ℝ) - y))) N hs]
  simpa only [Nat.cast_add, Nat.cast_one] using (hasSum_harmonic_tail hy hNy).tsum_eq

/-- All three negative-shift powers retain the source's exact tail convention. -/
theorem source_harmonic_tail_power_eq {N k : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    (∑' ν : ℕ, if N < ν then 1 / ((ν : ℝ) * ((ν : ℝ) - y) ^ k) else 0) =
      ∑' n : ℕ, 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y) ^ k) := by
  have hs : Summable (fun n : ℕ =>
      1 / ((↑(n + N + 1) : ℝ) * (↑(n + N + 1) - y) ^ k)) := by
    rcases hk with rfl | rfl | rfl
    · simpa only [Nat.cast_add, Nat.cast_one, pow_one] using
        (hasSum_harmonic_tail hy hNy).summable
    · simpa only [Nat.cast_add, Nat.cast_one] using
        (hasSum_harmonic_tail_square hy hNy).summable
    · simpa only [Nat.cast_add, Nat.cast_one] using
        (hasSum_harmonic_tail_cube hy hNy).summable
  rw [tsum_nat_tail_eq (F := fun ν : ℕ => 1 / ((ν : ℝ) * ((ν : ℝ) - y) ^ k)) N hs]
  simp only [Nat.cast_add, Nat.cast_one]

/-- All three positive-shift powers retain the source's exact positive-index convention. -/
theorem source_harmonic_plus_power_eq {k : ℕ} {y : ℝ} (hy : 0 < y)
    (hk : k = 1 ∨ k = 2 ∨ k = 3) :
    (∑' ν : ℕ, if 0 < ν then 1 / ((ν : ℝ) * ((ν : ℝ) + y) ^ k) else 0) =
      ∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ k) := by
  have hs : Summable (fun n : ℕ =>
      1 / ((↑(n + 0 + 1) : ℝ) * (↑(n + 0 + 1) + y) ^ k)) := by
    rcases hk with rfl | rfl | rfl
    · simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one, pow_one] using
        (hasSum_harmonic_plus hy).summable
    · simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one] using
        (hasSum_harmonic_plus_square hy).summable
    · simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one] using
        (hasSum_harmonic_plus_cube hy).summable
  rw [tsum_nat_tail_eq (F := fun ν : ℕ => 1 / ((ν : ℝ) * ((ν : ℝ) + y) ^ k)) 0 hs]
  simp only [Nat.add_zero, Nat.cast_add, Nat.cast_one]

end DhimanKadiriQuesadaHerrera2026
