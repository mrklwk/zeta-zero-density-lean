module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.HarmonicDigamma
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Alternating harmonic tails

Appendix Lemma 11 uses the actual digamma duplication formula and convergent
paired reciprocal differences. Pairing avoids interpreting a conditionally
convergent reciprocal series as an unordered sum.
-/

namespace DhimanKadiriQuesadaHerrera2026

open scoped BigOperators Topology
open Filter

private theorem ne_pole_of_re_pos {z : ℂ} (hz : 0 < z.re) : ∀ n : ℕ, z ≠ -n := by
  intro n h
  have hr := congrArg Complex.re h
  simp only [Complex.neg_re, Complex.natCast_re] at hr
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- Digamma duplication obtained by differentiating Mathlib's exact Gamma identity. -/
theorem digamma_two_mul {z : ℂ} (hz : 0 < z.re) :
    Complex.digamma (2 * z) = Complex.digamma z / 2 +
      Complex.digamma (z + 1 / 2) / 2 + Complex.log 2 := by
  have hzhalf : 0 < (z + 1 / 2).re := by simp; linarith
  have hz2 : 0 < (2 * z).re := by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hz
  have hd := Complex.differentiableAt_Gamma z (ne_pole_of_re_pos hz)
  have hdhalf := Complex.differentiableAt_Gamma (z + 1 / 2) (ne_pole_of_re_pos hzhalf)
  have hd2 := Complex.differentiableAt_Gamma (2 * z) (ne_pole_of_re_pos hz2)
  have hp : (2 : ℂ) ^ (1 - 2 * z) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  have hdp : DifferentiableAt ℂ (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w)) z :=
    ((differentiableAt_const (1 : ℂ)).sub (differentiableAt_id.const_mul 2)).const_cpow
      (Or.inl (by norm_num))
  have he : (fun w : ℂ => Complex.Gamma w * Complex.Gamma (w + 1 / 2)) =
      (fun w => Complex.Gamma (2 * w) * (2 : ℂ) ^ (1 - 2 * w) *
        (Real.sqrt Real.pi : ℂ)) := funext Complex.Gamma_mul_Gamma_add_half
  have h := congrArg (fun f : ℂ → ℂ => logDeriv f z) he
  rw [logDeriv_fun_mul (f := Complex.Gamma) (g := fun w => Complex.Gamma (w + 1 / 2))
    z (Complex.Gamma_ne_zero (ne_pole_of_re_pos hz))
    (Complex.Gamma_ne_zero (ne_pole_of_re_pos hzhalf)) hd
    (hdhalf.comp z (differentiableAt_id.add_const _)),
    logDeriv_mul_const z _ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'),
    logDeriv_fun_mul (f := fun w => Complex.Gamma (2 * w))
      (g := fun w => (2 : ℂ) ^ (1 - 2 * w)) z
      (Complex.Gamma_ne_zero (ne_pole_of_re_pos hz2)) hp
      (hd2.comp z (differentiableAt_id.const_mul 2)) hdp] at h
  have hhalf : logDeriv (fun w : ℂ => Complex.Gamma (w + 1 / 2)) z =
      Complex.digamma (z + 1 / 2) := by
    change logDeriv (Complex.Gamma ∘ (fun w : ℂ => w + 1 / 2)) z = _
    rw [logDeriv_comp (g := fun w : ℂ => w + 1 / 2) (x := z)
      hdhalf (differentiableAt_id.add_const _)]
    simp [Complex.digamma_def]
  have hdouble : logDeriv (fun w : ℂ => Complex.Gamma (2 * w)) z =
      Complex.digamma (2 * z) * 2 := by
    change logDeriv (Complex.Gamma ∘ (fun w : ℂ => 2 * w)) z = _
    rw [logDeriv_comp (g := fun w : ℂ => 2 * w) (x := z)
      hd2 (differentiableAt_id.const_mul _)]
    simp [Complex.digamma_def]
  have hpower : logDeriv (fun w : ℂ => (2 : ℂ) ^ (1 - 2 * w)) z =
      -2 * Complex.log 2 := by
    rw [logDeriv_apply, Complex.deriv_const_cpow (f := fun w : ℂ => 1 - 2 * w)
      (x := z) (by fun_prop)]
    rw [mul_div_cancel_right₀ _ hp]
    simp
    ring
  rw [hhalf, hdouble, hpower, ← Complex.digamma_def] at h
  linear_combination -h / 2

/-- The exact real duplication formula on its positive domain. -/
theorem real_digamma_two_mul {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (2 * x : ℝ)).re = (Complex.digamma (x : ℂ)).re / 2 +
      (Complex.digamma (x + 1 / 2 : ℝ)).re / 2 + Real.log 2 := by
  have h := congrArg Complex.re (digamma_two_mul (z := (x : ℂ)) hx)
  simpa [Complex.log_re, Complex.norm_ofNat] using h

/-- The absolutely convergent paired reciprocal series in the appendix. -/
theorem hasSum_paired_reciprocal {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 1 / (2 * (n : ℝ) + x) - 1 / (2 * (n : ℝ) + 1 + x))
      (((Complex.digamma ((x + 1) / 2 : ℝ)).re -
        (Complex.digamma (x / 2 : ℝ)).re) / 2) := by
  have h := (hasSum_digamma_difference (by positivity : 0 < x / 2)
    (by positivity : 0 < (x + 1) / 2)).div_const 2
  convert h using 1
  funext n
  have h1 : 2 * (n : ℝ) + x ≠ 0 := by positivity
  have h2 : 2 * (n : ℝ) + 1 + x ≠ 0 := by positivity
  have h3 : (n : ℝ) + x / 2 ≠ 0 := by positivity
  have h4 : (n : ℝ) + (x + 1) / 2 ≠ 0 := by positivity
  field_simp
  ring

private theorem reciprocal_sub_succ {u : ℝ} (hu : 0 < u) :
    1 / u - 1 / (u + 1) = 1 / (u * (u + 1)) := by
  have hu1 : u + 1 ≠ 0 := by positivity
  field_simp
  ring

private theorem hasSum_reciprocal_unit_difference {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + x) - 1 / ((↑(n + 1) : ℝ) + x)) (1 / x) := by
  have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + x)) atTop (𝓝 0) := by
    simpa only [one_div, Pi.inv_def] using
      (tendsto_atTop_add_const_right atTop x tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  have hn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + x) - 1 / ((↑(n + 1) : ℝ) + x) := by
    intro n
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    linarith
  apply (hasSum_iff_tendsto_nat_of_nonneg hn _).mpr
  simpa only [Finset.sum_range_sub', Nat.cast_zero, zero_add, sub_zero] using
    (tendsto_const_nhds (x := 1 / x)).sub hlim

/-- Elementary upper and lower bounds on the paired reciprocal value. -/
theorem paired_reciprocal_bounds {x : ℝ} (hx : 0 < x) :
    0 ≤ ((Complex.digamma ((x + 1) / 2 : ℝ)).re -
        (Complex.digamma (x / 2 : ℝ)).re) / 2 ∧
      ((Complex.digamma ((x + 1) / 2 : ℝ)).re -
        (Complex.digamma (x / 2 : ℝ)).re) / 2 ≤ 1 / x := by
  have hs := hasSum_paired_reciprocal hx
  have ht := hasSum_reciprocal_unit_difference hx
  rw [← hs.tsum_eq]
  constructor
  · apply tsum_nonneg
    intro n
    apply sub_nonneg.mpr
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  · rw [← ht.tsum_eq]
    apply hs.summable.tsum_le_tsum _ ht.summable
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show 2 * (n : ℝ) + 1 + x = (2 * (n : ℝ) + x) + 1 by ring,
      show (n : ℝ) + 1 + x = ((n : ℝ) + x) + 1 by ring,
      reciprocal_sub_succ (by positivity : 0 < 2 * (n : ℝ) + x),
      reciprocal_sub_succ (by positivity : 0 < (n : ℝ) + x)]
    apply one_div_le_one_div_of_le (by positivity)
    gcongr <;> linarith

/-- Duplication puts the paired reciprocal value in exactly the source's variables. -/
theorem paired_reciprocal_source_eq {x : ℝ} (hx : 0 < x) :
    ((Complex.digamma ((x + 1) / 2 : ℝ)).re -
      (Complex.digamma (x / 2 : ℝ)).re) / 2 =
        Real.log 2 + (Complex.digamma ((x + 1) / 2 : ℝ)).re -
          (Complex.digamma (x : ℂ)).re := by
  have h := real_digamma_two_mul (by positivity : 0 < x / 2)
  rw [show 2 * (x / 2) = x by ring,
    show x / 2 + 1 / 2 = (x + 1) / 2 by ring] at h
  linarith

private theorem tsum_pair_nat {f : ℕ → ℝ} (hf : Summable f) :
    (∑' n, f n) = ∑' n, (f (2 * n) + f (2 * n + 1)) := by
  have he := hf.comp_injective (show Function.Injective (fun n : ℕ => 2 * n) by
    intro n m h; dsimp only at h; omega)
  have ho := hf.comp_injective (show Function.Injective (fun n : ℕ => 2 * n + 1) by
    intro n m h; dsimp only at h; omega)
  dsimp only [Function.comp_def] at he ho
  rw [he.tsum_add ho]
  exact (tsum_even_add_odd he ho).symm

/-- Exact pairing of an absolutely convergent alternating reciprocal difference. -/
theorem alternating_reciprocal_difference {x a : ℝ} (hx : 0 < x) (ha : 0 < a) :
    (∑' n : ℕ, (-1 : ℝ) ^ n * (1 / ((n : ℝ) + x) - 1 / ((n : ℝ) + a))) =
      ((Complex.digamma ((x + 1) / 2 : ℝ)).re - (Complex.digamma (x / 2 : ℝ)).re) / 2 -
      ((Complex.digamma ((a + 1) / 2 : ℝ)).re - (Complex.digamma (a / 2 : ℝ)).re) / 2 := by
  rw [tsum_pair_nat (hasSum_digamma_difference hx ha).summable.alternating]
  calc
    _ = ∑' n : ℕ,
        ((1 / (2 * (n : ℝ) + x) - 1 / (2 * (n : ℝ) + 1 + x)) -
          (1 / (2 * (n : ℝ) + a) - 1 / (2 * (n : ℝ) + 1 + a))) := by
      apply tsum_congr
      intro n
      norm_num [pow_add]
      ring
    _ = _ := ((hasSum_paired_reciprocal hx).sub (hasSum_paired_reciprocal ha)).tsum_eq

/-- Exact alternating negative-shift tail, with the initial sign factored out. -/
theorem hasSum_alternating_harmonic_tail {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) :
    let δ : ℝ := (N : ℝ) + 1 - y
    HasSum (fun n : ℕ => (-1 : ℝ) ^ n /
      (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y)))
      ((((Complex.digamma ((δ + 1) / 2 : ℝ)).re -
          (Complex.digamma (δ / 2 : ℝ)).re) / 2 -
        ((Complex.digamma (((N : ℝ) + 2) / 2 : ℝ)).re -
          (Complex.digamma (((N : ℝ) + 1) / 2 : ℝ)).re) / 2) / y) := by
  dsimp only
  have hd : 0 < (N : ℝ) + 1 - y := by linarith
  have ha : 0 < (N : ℝ) + 1 := by positivity
  have hs := (hasSum_digamma_difference hd ha).summable.alternating.hasSum
  rw [alternating_reciprocal_difference hd ha] at hs
  convert hs.div_const y using 1
  · funext n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have h1 : (n : ℝ) + N + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + N + 1 - y ≠ 0 := by linarith
    have h3 : (n : ℝ) + ((N : ℝ) + 1 - y) ≠ 0 := by positivity
    have h4 : (n : ℝ) + ((N : ℝ) + 1) ≠ 0 := by positivity
    field_simp
    ring
  · rw [show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring]

/-- Appendix Lemma 11's negative-shift bound before restoring the initial unit sign. -/
theorem alternating_harmonic_tail_bound {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) :
    let δ : ℝ := (N : ℝ) + 1 - y
    |∑' n : ℕ, (-1 : ℝ) ^ n / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y))| ≤
      |(Complex.digamma (δ : ℂ)).re -
        (Complex.digamma ((δ + 1) / 2 : ℝ)).re - Real.log 2| / y +
        1 / (y * ((N : ℝ) + 1)) := by
  dsimp only
  let d (u : ℝ) := ((Complex.digamma ((u + 1) / 2 : ℝ)).re -
    (Complex.digamma (u / 2 : ℝ)).re) / 2
  have hd : 0 < (N : ℝ) + 1 - y := by linarith
  have ha : 0 < (N : ℝ) + 1 := by positivity
  have hs : (∑' n : ℕ, (-1 : ℝ) ^ n /
      (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y))) =
      (d ((N : ℝ) + 1 - y) - d ((N : ℝ) + 1)) / y := by
    simpa only [d, show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring] using
      (hasSum_alternating_harmonic_tail hy hNy).tsum_eq
  have hda : |d ((N : ℝ) + 1)| ≤ 1 / ((N : ℝ) + 1) := by
    rw [abs_of_nonneg (paired_reciprocal_bounds ha).1]
    exact (paired_reciprocal_bounds ha).2
  have hdδ : d ((N : ℝ) + 1 - y) =
      -((Complex.digamma ((N : ℝ) + 1 - y : ℝ)).re -
        (Complex.digamma (((N : ℝ) + 1 - y + 1) / 2 : ℝ)).re - Real.log 2) := by
    dsimp only [d]
    rw [paired_reciprocal_source_eq hd]
    ring
  rw [hs, abs_div, abs_of_pos hy]
  calc
    _ ≤ (|d ((N : ℝ) + 1 - y)| + 1 / ((N : ℝ) + 1)) / y :=
      div_le_div_of_nonneg_right ((abs_sub _ _).trans (add_le_add_right hda _)) hy.le
    _ = _ := by
      rw [hdδ, abs_neg]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- Restoring an integer shift in the alternating sign preserves the absolute sum. -/
theorem abs_tsum_alternating_shift (f : ℕ → ℝ) (M : ℕ) :
    |∑' n : ℕ, (-1 : ℝ) ^ (n + M) * f n| = |∑' n : ℕ, (-1 : ℝ) ^ n * f n| := by
  have he : (∑' n : ℕ, (-1 : ℝ) ^ (n + M) * f n) =
      (-1 : ℝ) ^ M * ∑' n : ℕ, (-1 : ℝ) ^ n * f n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [pow_add]
    ring
  rw [he, abs_mul, abs_pow]
  norm_num

/-- Exact positive-shift alternating tail with its negative initial term. -/
theorem hasSum_alternating_harmonic_plus {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y)))
      ((((Complex.digamma ((y + 2) / 2 : ℝ)).re -
        (Complex.digamma ((y + 1) / 2 : ℝ)).re) / 2 - Real.log 2) / y) := by
  have ha : 0 < y + 1 := by positivity
  have hs := (hasSum_digamma_difference (by norm_num : (0 : ℝ) < 1) ha).summable.alternating.hasSum
  rw [alternating_reciprocal_difference (by norm_num : (0 : ℝ) < 1) ha,
    paired_reciprocal_source_eq (by norm_num : (0 : ℝ) < 1)] at hs
  norm_num at hs
  convert hs.neg.div_const y using 1
  · funext n
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 1 + y ≠ 0 := by positivity
    have h3 : (n : ℝ) + (y + 1) ≠ 0 := by positivity
    rw [pow_succ]
    field_simp
    ring
  · push_cast
    rw [show (y : ℂ) + 1 + 1 = (y : ℂ) + 2 by ring]
    ring

/-- The corrected appendix identity, preserving the omitted `-2 log 2` term. -/
theorem alternating_harmonic_plus_identity {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))) =
      ((Complex.digamma (y + 1 : ℝ)).re -
        (Complex.digamma ((y + 1) / 2 : ℝ)).re - 2 * Real.log 2) / y := by
  rw [(hasSum_alternating_harmonic_plus hy).tsum_eq]
  have h := real_digamma_two_mul (by positivity : 0 < (y + 1) / 2)
  rw [show 2 * ((y + 1) / 2) = y + 1 by ring,
    show (y + 1) / 2 + 1 / 2 = (y + 2) / 2 by ring] at h
  congr 1
  linarith

/-- Appendix Lemma 11's positive-shift absolute bound with the printed constant. -/
theorem alternating_harmonic_plus_bound {y : ℝ} (hy : 0 < y) :
    |∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))| ≤
      Real.log 2 / y + 3 / (2 * y * (y + 1)) := by
  rw [(hasSum_alternating_harmonic_plus hy).tsum_eq, abs_div, abs_of_pos hy]
  have hb := paired_reciprocal_bounds (by positivity : 0 < y + 1)
  rw [show y + 1 + 1 = y + 2 by ring] at hb
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc
    _ ≤ (1 / (y + 1) + Real.log 2) / y := by
      apply div_le_div_of_nonneg_right _ hy.le
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg hb.1, abs_of_nonneg hlog]
      linarith [hb.2]
    _ ≤ _ := by
      field_simp
      nlinarith

/-- The actual special value at one, from Mathlib. -/
theorem real_digamma_one : (Complex.digamma 1).re = -Real.eulerMascheroniConstant := by
  simp [Complex.digamma_one]

/-- The actual special value at one half, from Mathlib. -/
theorem real_digamma_half :
    (Complex.digamma (1 / 2)).re = -2 * Real.log 2 - Real.eulerMascheroniConstant := by
  rw [Complex.digamma_one_half]
  simp [Complex.log_re]

/-- The real recurrence on the positive axis, from Mathlib. -/
theorem real_digamma_add_one {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (x + 1 : ℝ)).re = (Complex.digamma (x : ℂ)).re + 1 / x := by
  have h := congrArg Complex.re (Complex.digamma_apply_add_one (x : ℂ) (ne_pole_of_re_pos hx))
  simpa using h

/-- The real part used in the estimates is the source's real Gamma logarithmic derivative. -/
theorem real_digamma_eq_deriv_Gamma_div {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (x : ℂ)).re = deriv Real.Gamma x / Real.Gamma x := by
  have h := (Complex.differentiableAt_Gamma (x : ℂ)
    (ne_pole_of_re_pos hx)).hasDerivAt.real_of_complex.deriv
  change deriv Real.Gamma x = (deriv Complex.Gamma (x : ℂ)).re at h
  rw [Complex.digamma_def, logDeriv_apply, Complex.Gamma_ofReal]
  simp [← h]

/-- Appendix Lemma 11's first estimate on the literal source tail, including `N = 0`. -/
theorem source_alternating_harmonic_tail_bound {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) :
    let δ : ℝ := (N : ℝ) + 1 - y
    |∑' ν : ℕ, if N < ν then (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) - y)) else 0| ≤
      |(Complex.digamma (δ : ℂ)).re -
        (Complex.digamma ((δ + 1) / 2 : ℝ)).re - Real.log 2| / y +
        1 / (y * ((N : ℝ) + 1)) := by
  dsimp only
  have hs : Summable (fun n : ℕ => (-1 : ℝ) ^ (n + N + 1) /
      ((↑(n + N + 1) : ℝ) * (↑(n + N + 1) - y))) := by
    have h := (hasSum_alternating_harmonic_tail hy hNy).summable.mul_left
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
  exact alternating_harmonic_tail_bound hy hNy

/-- Appendix Lemma 11's second estimate on the literal positive-index series. -/
theorem source_alternating_harmonic_plus_bound {y : ℝ} (hy : 0 < y) :
    |∑' ν : ℕ, if 0 < ν then (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) + y)) else 0| ≤
      Real.log 2 / y + 3 / (2 * y * (y + 1)) := by
  have hs : Summable (fun n : ℕ => (-1 : ℝ) ^ (n + 0 + 1) /
      ((↑(n + 0 + 1) : ℝ) * (↑(n + 0 + 1) + y))) := by
    simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one] using
      (hasSum_alternating_harmonic_plus hy).summable
  rw [tsum_nat_tail_eq (F := fun ν : ℕ => (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) + y))) 0 hs]
  simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one] using alternating_harmonic_plus_bound hy

/-- The corrected appendix identity on the actual positive-index series. -/
theorem source_alternating_harmonic_plus_identity {y : ℝ} (hy : 0 < y) :
    (∑' ν : ℕ, if 0 < ν then (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) + y)) else 0) =
      ((Complex.digamma (y + 1 : ℝ)).re -
        (Complex.digamma ((y + 1) / 2 : ℝ)).re - 2 * Real.log 2) / y := by
  have hs : Summable (fun n : ℕ => (-1 : ℝ) ^ (n + 0 + 1) /
      ((↑(n + 0 + 1) : ℝ) * (↑(n + 0 + 1) + y))) := by
    simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one] using
      (hasSum_alternating_harmonic_plus hy).summable
  rw [tsum_nat_tail_eq (F := fun ν : ℕ => (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) + y))) 0 hs]
  simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one] using alternating_harmonic_plus_identity hy

/-- The appendix identity without its logarithmic correction is false for every positive shift. -/
theorem not_printed_alternating_plus_identity {y : ℝ} (hy : 0 < y) :
    (∑' ν : ℕ, if 0 < ν then (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) + y)) else 0) ≠
      ((Complex.digamma (y + 1 : ℝ)).re -
        (Complex.digamma ((y + 1) / 2 : ℝ)).re) / y := by
  rw [source_alternating_harmonic_plus_identity hy]
  intro h
  have he := congrArg (fun u : ℝ => u * y) h
  simp only [div_mul_cancel₀ _ hy.ne'] at he
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  linarith

end DhimanKadiriQuesadaHerrera2026
