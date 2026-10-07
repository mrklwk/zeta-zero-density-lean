module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.FiniteExponentialSums

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # The actual convergent oscillatory tails of Lemma 3 -/

namespace DhimanKadiriQuesadaHerrera2026

open scoped BigOperators Topology

/-- Translation of an actual Fourier mode multiplies by a unit-norm mode. -/
theorem expMode_add (x : ℝ) (m n : ℕ) :
    expMode x (m + n) = expMode x m * expMode x n := by
  unfold expMode
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Every consecutive positive-index block has the same geometric majorant. -/
theorem norm_shifted_mode_prefix_le {x : ℝ} (hx : Real.sin (Real.pi * x) ≠ 0)
    (N M : ℕ) :
    ‖∑ n ∈ Finset.range M, expMode x (n + N + 1)‖ ≤ 1 / |Real.sin (Real.pi * x)| := by
  have he (n : ℕ) : expMode x (n + N + 1) = expMode x N * expMode x (n + 1) := by
    rw [show n + N + 1 = N + (n + 1) by omega, expMode_add]
  simp_rw [he]
  rw [← Finset.mul_sum, norm_mul, norm_expMode, one_mul, ← sum_Icc_one_eq_sum_range,
    norm_finite_mode_sum hx]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)

/-- Absolute convergence of summable nonnegative weights times the actual modes. -/
theorem summable_weighted_modes {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hs : Summable w) (x : ℝ) (N : ℕ) :
    Summable (fun n : ℕ => w n • expMode x (n + N + 1)) := by
  apply hs.of_norm_bounded
  intro n
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw n), norm_expMode, mul_one,
    le_refl]

/-- The finite Abel bound passes to absolutely convergent weighted mode tails. -/
theorem norm_tsum_weighted_modes_le {w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (ha : Antitone w) (hs : Summable w) {x : ℝ}
    (hx : Real.sin (Real.pi * x) ≠ 0) (N : ℕ) :
    ‖∑' n : ℕ, w n • expMode x (n + N + 1)‖ ≤ w 0 / |Real.sin (Real.pi * x)| := by
  have ht := (summable_weighted_modes hw hs x N).hasSum.tendsto_sum_nat.norm
  have hb := norm_weighted_sum_le hw ha (norm_shifted_mode_prefix_le hx N)
  simpa only [mul_one_div] using le_of_tendsto' ht hb

/-- The actual negative-shift denominator is positive and its reciprocal decreases. -/
theorem antitone_negative_tail_weight {N : ℕ} {y : ℝ} (hNy : y < (N : ℝ) + 1) :
    Antitone (fun n : ℕ => 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y))) := by
  intro n m hnm
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  apply one_div_le_one_div_of_le (mul_pos (by positivity) (by linarith))
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)

/-- The actual positive-shift reciprocal weight decreases for all positive y. -/
theorem antitone_positive_tail_weight {y : ℝ} (hy : 0 < y) :
    Antitone (fun n : ℕ => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))) := by
  intro n m hnm
  have hnm' : (n : ℝ) ≤ m := Nat.cast_le.mpr hnm
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

/-- A stronger Abel bound for the actual negative-shift tail. -/
theorem norm_negative_tail_le {N : ℕ} {x y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) (hx : Real.sin (Real.pi * x) ≠ 0) :
    ‖∑' n : ℕ, (1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y))) •
      expMode x (n + N + 1)‖ ≤
        1 / (((N : ℝ) + 1) * ((N : ℝ) + 1 - y)) / |Real.sin (Real.pi * x)| := by
  have hw (n : ℕ) : 0 ≤ 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y)) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    apply one_div_nonneg.mpr
    exact mul_nonneg (by positivity) (by linarith)
  simpa using norm_tsum_weighted_modes_le hw (antitone_negative_tail_weight hNy)
    (hasSum_harmonic_tail hy hNy).summable hx N

/-- A stronger Abel bound for the actual positive-shift tail. -/
theorem norm_positive_tail_le {x y : ℝ} (hy : 0 < y)
    (hx : Real.sin (Real.pi * x) ≠ 0) :
    ‖∑' n : ℕ, (1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))) • expMode x (n + 1)‖ ≤
      1 / (1 + y) / |Real.sin (Real.pi * x)| := by
  have hw (n : ℕ) : 0 ≤ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y)) := by positivity
  simpa using norm_tsum_weighted_modes_le hw (antitone_positive_tail_weight hy)
    (hasSum_harmonic_plus hy).summable hx 0

/-- Reindex a complex natural-number tail, retaining its precise source inequality. -/
theorem tsum_complex_nat_tail_eq {F : ℕ → ℂ} (N : ℕ)
    (hF : Summable (fun n : ℕ => F (n + N + 1))) :
    (∑' ν : ℕ, if N < ν then F ν else 0) = ∑' n : ℕ, F (n + N + 1) := by
  let f : ℕ → ℂ := fun ν => if N < ν then F ν else 0
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

/-- The source's actual negative-shift oscillatory tail. -/
noncomputable def negativeTail (N : ℕ) (x y : ℝ) : ℂ :=
  ∑' ν : ℕ, if N < ν then expMode x ν / (((ν : ℝ) * ((ν : ℝ) - y) : ℝ) : ℂ) else 0

/-- The source's actual positive-shift oscillatory tail. -/
noncomputable def positiveTail (x y : ℝ) : ℂ :=
  ∑' ν : ℕ, if 0 < ν then expMode x ν / (((ν : ℝ) * ((ν : ℝ) + y) : ℝ) : ℂ) else 0

/-- The mixed negative-shift denominator makes the actual series absolutely convergent. -/
theorem summable_negative_tail_shift {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) (x : ℝ) :
    Summable (fun n : ℕ => expMode x (n + N + 1) /
      (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y) : ℝ)) := by
  have hw (n : ℕ) : 0 ≤ 1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y)) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    apply one_div_nonneg.mpr
    exact mul_nonneg (by positivity) (by linarith)
  have h := summable_weighted_modes hw (hasSum_harmonic_tail hy hNy).summable x N
  simpa [Complex.real_smul, mul_comm, div_eq_mul_inv] using h

/-- Reindexing the actual negative tail preserves its first included frequency. -/
theorem negativeTail_eq_shift {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) (x : ℝ) :
    negativeTail N x y = ∑' n : ℕ,
      (1 / (((n : ℝ) + N + 1) * ((n : ℝ) + N + 1 - y))) • expMode x (n + N + 1) := by
  unfold negativeTail
  rw [tsum_complex_nat_tail_eq (F := fun ν : ℕ =>
    expMode x ν / (((ν : ℝ) * ((ν : ℝ) - y) : ℝ) : ℂ)) N
    (by simpa only [Nat.cast_add, Nat.cast_one] using summable_negative_tail_shift hy hNy x)]
  apply tsum_congr
  intro n
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Absolute convergence of the actual positive-shift series. -/
theorem summable_positive_tail_shift {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun n : ℕ => expMode x (n + 1) /
      (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) : ℝ)) := by
  have hw (n : ℕ) : 0 ≤ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y)) := by positivity
  have h := summable_weighted_modes hw (hasSum_harmonic_plus hy).summable x 0
  simpa [Complex.real_smul, mul_comm, div_eq_mul_inv] using h

/-- Reindexing the positive tail starts at one, not zero or two. -/
theorem positiveTail_eq_shift {y : ℝ} (hy : 0 < y) (x : ℝ) :
    positiveTail x y = ∑' n : ℕ,
      (1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y))) • expMode x (n + 1) := by
  unfold positiveTail
  rw [tsum_complex_nat_tail_eq (F := fun ν : ℕ =>
    expMode x ν / (((ν : ℝ) * ((ν : ℝ) + y) : ℝ) : ℂ)) 0
    (by simpa only [Nat.add_zero, Nat.cast_add, Nat.cast_one] using
      summable_positive_tail_shift hy x)]
  apply tsum_congr
  intro n
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Lemma 3's exact generic negative-shift majorant. -/
theorem norm_negativeTail_le_source {N : ℕ} {x y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    ‖negativeTail N x y‖ ≤ (1 / (y * |Real.sin (Real.pi * x)|)) *
      (1 / ((N : ℝ) + 1 - y) + 1 / ((N : ℝ) + 1)) := by
  rw [negativeTail_eq_shift hy hNy]
  have ha : 0 < (N : ℝ) + 1 := by positivity
  have hd : 0 < (N : ℝ) + 1 - y := by linarith
  have he : (1 / y) * (1 / ((N : ℝ) + 1 - y) + 1 / ((N : ℝ) + 1)) =
      1 / (((N : ℝ) + 1) * ((N : ℝ) + 1 - y)) + 2 / (y * ((N : ℝ) + 1)) := by
    field_simp
    ring
  have hb : 1 / (((N : ℝ) + 1) * ((N : ℝ) + 1 - y)) ≤
      (1 / y) * (1 / ((N : ℝ) + 1 - y) + 1 / ((N : ℝ) + 1)) := by
    rw [he]
    linarith [show 0 ≤ 2 / (y * ((N : ℝ) + 1)) by positivity]
  have h := (norm_negative_tail_le hy hNy (sin_pi_mul_ne_zero_of_noninteger hx)).trans
    (div_le_div_of_nonneg_right hb (abs_nonneg (Real.sin (Real.pi * x))))
  convert h using 1
  ring

/-- Lemma 3's exact generic positive-shift majorant. -/
theorem norm_positiveTail_le_source {x y : ℝ} (hy : 0 < y)
    (hx : ∀ k : ℤ, x ≠ (k : ℝ)) :
    ‖positiveTail x y‖ ≤ (1 / (y * |Real.sin (Real.pi * x)|)) * (1 + 1 / (1 + y)) := by
  rw [positiveTail_eq_shift hy]
  have he : (1 / y) * (1 + 1 / (1 + y)) = 1 / (1 + y) + 2 / (y * (1 + y)) := by
    have h1 : 0 < 1 + y := by positivity
    field_simp
    ring
  have hb : 1 / (1 + y) ≤ (1 / y) * (1 + 1 / (1 + y)) := by
    rw [he]
    linarith [show 0 ≤ 2 / (y * (1 + y)) by positivity]
  have h := (norm_positive_tail_le hy (sin_pi_mul_ne_zero_of_noninteger hx)).trans
    (div_le_div_of_nonneg_right hb (abs_nonneg (Real.sin (Real.pi * x))))
  convert h using 1
  ring

/-- Differentiating the actual Gamma reflection identity gives the real digamma reflection. -/
theorem real_digamma_one_sub {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    (Complex.digamma (1 - x : ℝ)).re - (Complex.digamma (x : ℂ)).re =
      Real.pi * Real.cos (Real.pi * x) / Real.sin (Real.pi * x) := by
  have hx' : 0 < 1 - x := by linarith
  have hd : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (fun n => by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hd' : DifferentiableAt ℝ Real.Gamma (1 - x) :=
    Real.differentiableAt_Gamma (fun n => by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hsin : Real.sin (Real.pi * x) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx)
      (by nlinarith [Real.pi_pos])).ne'
  have he : (fun u : ℝ => Real.Gamma u * Real.Gamma (1 - u)) =
      (fun u => Real.pi / Real.sin (Real.pi * u)) := funext Real.Gamma_mul_Gamma_one_sub
  have h := congrArg (fun f : ℝ → ℝ => logDeriv f x) he
  rw [logDeriv_fun_mul (f := Real.Gamma) (g := fun u : ℝ => Real.Gamma (1 - u)) x (Real.Gamma_pos_of_pos hx).ne' (Real.Gamma_pos_of_pos hx').ne'
      hd (hd'.comp x ((differentiableAt_const (1 : ℝ)).sub differentiableAt_id)),
    logDeriv_fun_div (f := fun _ : ℝ => Real.pi) (g := fun u => Real.sin (Real.pi * u)) x Real.pi_ne_zero hsin (differentiableAt_const _) (by fun_prop),
    logDeriv_const, Pi.zero_apply, zero_sub] at h
  have hcomp : logDeriv (fun u : ℝ => Real.Gamma (1 - u)) x = -logDeriv Real.Gamma (1 - x) := by
    change logDeriv (Real.Gamma ∘ (fun u : ℝ => 1 - u)) x = _
    rw [logDeriv_comp hd' ((differentiableAt_const (1 : ℝ)).sub differentiableAt_id)]
    simp
  have htrig : logDeriv (fun u : ℝ => Real.sin (Real.pi * u)) x =
      Real.pi * Real.cos (Real.pi * x) / Real.sin (Real.pi * x) := by
    change logDeriv (Real.sin ∘ (fun u : ℝ => Real.pi * u)) x = _
    rw [logDeriv_comp (by fun_prop) (by fun_prop), Real.logDeriv_sin]
    simp [Real.cot_eq_cos_div_sin]
    ring
  rw [hcomp, htrig, logDeriv_apply, logDeriv_apply,
    ← real_digamma_eq_deriv_Gamma_div hx, ← real_digamma_eq_deriv_Gamma_div hx'] at h
  linarith

/-- The paired reciprocal sum at one half has the exact value pi/2. -/
theorem paired_reciprocal_half :
    ((Complex.digamma (3 / 4 : ℝ)).re - (Complex.digamma (1 / 4 : ℝ)).re) / 2 =
      Real.pi / 2 := by
  have h := real_digamma_one_sub (by norm_num : (0 : ℝ) < 1 / 4) (by norm_num)
  norm_num at h
  rw [show Real.pi * (1 / 4) = Real.pi / 4 by ring,
    Real.cos_pi_div_four, Real.sin_pi_div_four] at h
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have he : Real.pi * (Real.sqrt 2 / 2) / (Real.sqrt 2 / 2) = Real.pi := by
    field_simp
  rw [he] at h
  norm_num
  linarith

/-- The paired reciprocal value decreases on its positive domain. -/
theorem paired_reciprocal_antitone {x z : ℝ} (hx : 0 < x) (hxz : x ≤ z) :
    ((Complex.digamma ((z + 1) / 2 : ℝ)).re - (Complex.digamma (z / 2 : ℝ)).re) / 2 ≤
      ((Complex.digamma ((x + 1) / 2 : ℝ)).re - (Complex.digamma (x / 2 : ℝ)).re) / 2 := by
  have hz : 0 < z := hx.trans_le hxz
  rw [← (hasSum_paired_reciprocal hz).tsum_eq, ← (hasSum_paired_reciprocal hx).tsum_eq]
  apply (hasSum_paired_reciprocal hz).summable.tsum_le_tsum _ (hasSum_paired_reciprocal hx).summable
  intro n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have he (u : ℝ) (hu : 0 < u) : 1 / u - 1 / (u + 1) = 1 / (u * (u + 1)) := by
    have hu' : 0 < u + 1 := by positivity
    field_simp
    ring
  rw [show 2 * (n : ℝ) + 1 + z = (2 * (n : ℝ) + z) + 1 by ring,
    show 2 * (n : ℝ) + 1 + x = (2 * (n : ℝ) + x) + 1 by ring,
    he _ (by positivity), he _ (by positivity)]
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)

/-- The exact digamma expression in Lemma 3 is at most pi/2 for delta at least one half. -/
theorem digamma_half_integer_tail_bound {δ : ℝ} (hδ : 1 / 2 ≤ δ) :
    |(Complex.digamma (δ : ℂ)).re - (Complex.digamma ((δ + 1) / 2 : ℝ)).re - Real.log 2| ≤
      Real.pi / 2 := by
  have hd : 0 < δ := by linarith
  have he := paired_reciprocal_source_eq hd
  have hn := (paired_reciprocal_bounds hd).1
  have ha : |(Complex.digamma (δ : ℂ)).re -
      (Complex.digamma ((δ + 1) / 2 : ℝ)).re - Real.log 2| =
        ((Complex.digamma ((δ + 1) / 2 : ℝ)).re - (Complex.digamma (δ / 2 : ℝ)).re) / 2 := by
    rw [show (Complex.digamma (δ : ℂ)).re -
      (Complex.digamma ((δ + 1) / 2 : ℝ)).re - Real.log 2 =
        -(((Complex.digamma ((δ + 1) / 2 : ℝ)).re -
          (Complex.digamma (δ / 2 : ℝ)).re) / 2) by linarith, abs_neg, abs_of_nonneg hn]
  rw [ha]
  have h := paired_reciprocal_antitone (by norm_num : (0 : ℝ) < 1 / 2) hδ
  norm_num at h
  have hh := paired_reciprocal_half
  norm_num at hh
  push_cast
  linarith

/-- Convergence of the negative tail in the literal natural-number indexing. -/
theorem summable_negativeTail {N : ℕ} {y : ℝ} (hy : 0 < y)
    (hNy : y < (N : ℝ) + 1) (x : ℝ) :
    Summable (fun ν : ℕ => if N < ν then
      expMode x ν / (((ν : ℝ) * ((ν : ℝ) - y) : ℝ) : ℂ) else 0) := by
  apply (summable_nat_add_iff (N + 1)).mp
  have h := summable_negative_tail_shift hy hNy x
  convert h using 1
  funext n
  rw [ite_eq_left (by omega)]
  simp [add_assoc]

/-- Convergence of the positive tail in the literal positive-index convention. -/
theorem summable_positiveTail {y : ℝ} (hy : 0 < y) (x : ℝ) :
    Summable (fun ν : ℕ => if 0 < ν then
      expMode x ν / (((ν : ℝ) * ((ν : ℝ) + y) : ℝ) : ℂ) else 0) := by
  apply (summable_nat_add_iff 1).mp
  have h := summable_positive_tail_shift hy x
  convert h using 1
  funext n
  simp

/-- The actual half-integer negative tail is the real alternating source series. -/
theorem negativeTail_half_integer (N : ℕ) (k : ℤ) (y : ℝ) :
    negativeTail N ((k : ℝ) + 1 / 2) y =
      ((∑' ν : ℕ, if N < ν then (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) - y)) else 0 : ℝ) : ℂ) := by
  unfold negativeTail
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro ν
  split_ifs
  · rw [expMode_half_integer]
    simp
  · simp

/-- The actual half-integer positive tail is the real alternating source series. -/
theorem positiveTail_half_integer (k : ℤ) (y : ℝ) :
    positiveTail ((k : ℝ) + 1 / 2) y =
      ((∑' ν : ℕ, if 0 < ν then (-1 : ℝ) ^ ν / ((ν : ℝ) * ((ν : ℝ) + y)) else 0 : ℝ) : ℂ) := by
  unfold positiveTail
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro ν
  split_ifs
  · rw [expMode_half_integer]
    simp
  · simp

/-- The refined negative-tail bound in Lemma 3, with its exact digamma arguments. -/
theorem norm_negativeTail_half_integer_le {N : ℕ} (k : ℤ) {y : ℝ}
    (hy : 0 < y) (hNy : y < (N : ℝ) + 1) :
    let δ : ℝ := (N : ℝ) + 1 - y
    ‖negativeTail N ((k : ℝ) + 1 / 2) y‖ ≤
      |(Complex.digamma (δ : ℂ)).re -
        (Complex.digamma ((δ + 1) / 2 : ℝ)).re - Real.log 2| / y + 1 / (y * ((N : ℝ) + 1)) := by
  rw [negativeTail_half_integer, Complex.norm_real, Real.norm_eq_abs]
  exact source_alternating_harmonic_tail_bound hy hNy

/-- The explicit pi/2 consequence preserves the whole first omitted-frequency correction. -/
theorem norm_negativeTail_half_integer_le_pi {N : ℕ} (k : ℤ) {y : ℝ}
    (hy : 0 < y) (hδ : 1 / 2 ≤ (N : ℝ) + 1 - y) :
    ‖negativeTail N ((k : ℝ) + 1 / 2) y‖ ≤
      (1 / y) * (Real.pi / 2 + 1 / ((N : ℝ) + 1)) := by
  have hNy : y < (N : ℝ) + 1 := by linarith
  have hb := div_le_div_of_nonneg_right (digamma_half_integer_tail_bound hδ) hy.le
  have h := (norm_negativeTail_half_integer_le k hy hNy).trans
    (add_le_add_left hb (1 / (y * ((N : ℝ) + 1))))
  convert h using 1
  field_simp

/-- The refined positive-tail bound in Lemma 3, with coefficient three halves. -/
theorem norm_positiveTail_half_integer_le (k : ℤ) {y : ℝ} (hy : 0 < y) :
    ‖positiveTail ((k : ℝ) + 1 / 2) y‖ ≤ Real.log 2 / y + 3 / (2 * y * (y + 1)) := by
  rw [positiveTail_half_integer, Complex.norm_real, Real.norm_eq_abs]
  exact source_alternating_harmonic_plus_bound hy

end DhimanKadiriQuesadaHerrera2026
