module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.Analytic.ZetaContinuation
public import WeylPort.AFE.PoissonApplications
public import WeylPort.AFE.Objects

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Sharp zeta truncation and the actual AFE power integrals

The continuation identity is consumed from the existing node-71 foundation:
`Zeta0EqZeta` and `ZetaBnd_aux1b`, without duplicating their analytic continuation proofs.
-/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory Filter
open scoped Topology

/-- The existing Euler--Maclaurin continuation controls the actual regularized Dirichlet sum. -/
theorem norm_zeta_sub_regularized_sum_le {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s - ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
      (N : ℂ) ^ (1 - s) / (s - 1))‖ ≤
      (N : ℝ) ^ (-s.re) * (1 / 2 + ‖s‖ / s.re) := by
  have he := Zeta0EqZeta hN hs hs1
  unfold riemannZeta0 at he
  have hn : 0 < (N : ℝ) := by exact_mod_cast hN
  have hi := ZetaBnd_aux1b N hN (t := s.im) hs
  rw [Complex.re_add_im] at hi
  have hid : riemannZeta s - ((∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
      (N : ℂ) ^ (1 - s) / (s - 1)) = -(N : ℂ) ^ (-s) / 2 +
      s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1) := by
    rw [← he]
    have hd : 1 - s = -(s - 1) := by ring
    rw [hd, neg_div_neg_eq]
    ring
  rw [hid]
  calc
    _ ≤ ‖-(N : ℂ) ^ (-s) / 2‖ +
        ‖s * ∫ x in Set.Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖ := norm_add_le _ _
    _ ≤ (N : ℝ) ^ (-s.re) / 2 + ‖s‖ * ((N : ℝ) ^ (-s.re) / s.re) := by
      rw [norm_div, norm_neg, Complex.norm_ofNat, norm_mul]
      have hp : ‖(N : ℂ) ^ (-s)‖ = (N : ℝ) ^ (-s.re) := by
        simpa only [Complex.ofReal_natCast, Complex.neg_re] using
          Complex.norm_cpow_eq_rpow_re_of_pos hn (-s)
      rw [hp]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hi (norm_nonneg s))
    _ = _ := by ring

/-- Regularized finite Dirichlet sums converge to the actual zeta function throughout Re(s)>0. -/
theorem tendsto_regularized_sum {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) +
      (N : ℂ) ^ (1 - s) / (s - 1)) atTop (𝓝 (riemannZeta s)) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (-s.re)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) ?_
    (by simpa using hp.mul_const (1 / 2 + ‖s‖ / s.re))
  filter_upwards [eventually_gt_atTop 0] with N hN
  rw [norm_sub_rev]
  simpa only [one_div] using norm_zeta_sub_regularized_sum_le hN hs hs1

/-- The real logarithmic phase is the principal complex power, with the positive-height sign. -/
theorem weightedWave_afe_eq_cpow (sigma t : ℝ) {x : ℝ} (hx : 0 < x) :
    weightedWave (afePhase (t / (2 * Real.pi))) (afeWeight sigma) x =
      (x : ℂ) ^ (-(sigma : ℂ) + (t : ℂ) * Complex.I) := by
  unfold weightedWave afePhase afeWeight
  rw [Real.rpow_def_of_pos hx, Complex.ofReal_exp, Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le, ← Complex.exp_add]
  congr 1
  push_cast
  field_simp

/-- Conjugation supplies the negative sign in the actual Dirichlet term. -/
theorem conj_weightedWave_afe (sigma t : ℝ) {x : ℝ} (hx : 0 < x) :
    starRingEnd ℂ (weightedWave (afePhase (t / (2 * Real.pi))) (afeWeight sigma) x) =
      (x : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * Complex.I)) := by
  rw [weightedWave_afe_eq_cpow sigma t hx,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.exp_conj, ← Complex.ofReal_log hx.le]
  congr 1
  simp only [map_mul, map_add, map_neg, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- The finite Dirichlet integral has its actual antiderivative on every positive interval. -/
theorem integral_cpow_neg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) {s : ℂ} (hs : s ≠ 1) :
    (∫ x in a..b, (x : ℂ) ^ (-s)) =
      ((a : ℂ) ^ (1 - s) - (b : ℂ) ^ (1 - s)) / (s - 1) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    exact ha.not_ge h.1
  have hneg : -s ≠ -1 := by
    intro h
    apply hs
    linear_combination -h
  rw [integral_cpow (Or.inr ⟨hneg, h0⟩)]
  have he : -s + 1 = 1 - s := by ring
  rw [he]
  have hd : 1 - s = -(s - 1) := by ring
  rw [hd, div_neg]
  ring

/-- Positive integer interval sums agree exactly with their natural-number indexing. -/
theorem sum_int_Ioc_eq_nat_Ioc (F : ℝ → ℂ) (M N : ℕ) :
    (∑ n ∈ Finset.Ioc (M : ℤ) (N : ℤ), F (n : ℝ)) =
      ∑ n ∈ Finset.Ioc M N, F (n : ℝ) := by
  apply Finset.sum_bij (fun (n : ℤ) _ => n.toNat)
  · intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    constructor <;> omega
  · intro n hn m hm hnm
    simp only [Finset.mem_Ioc] at hn hm
    omega
  · intro n hn
    refine ⟨(n : ℤ), ?_, by simp only [Int.toNat_natCast]⟩
    simp only [Finset.mem_Ioc] at hn ⊢
    exact_mod_cast hn
  · intro n hn
    have hn0 : 0 ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hn0]

/-- Complex conjugation commutes with the actual oriented interval integral. -/
theorem conj_intervalIntegral (F : ℝ → ℂ) (a b : ℝ) :
    starRingEnd ℂ (∫ x in a..b, F x) = ∫ x in a..b, starRingEnd ℂ (F x) := by
  simp only [intervalIntegral, map_sub, integral_conj]

/-- The Poisson estimate expressed with the actual Dirichlet powers and their negative phase. -/
theorem afe_finite_cpow_bound {sigma t a b : ℝ} (hsigma : 0 ≤ sigma) (ht : 0 < t)
    (ha : 0 < a) (hab : a < b) (hcut : t / (2 * Real.pi) < a)
    (hahalf : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, (n : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * Complex.I))) -
      ∫ x in a..b, (x : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * Complex.I))‖ ≤
      a ^ (-sigma) / Real.pi * (1 + sigma / t) * afePartIFactor (t / (2 * Real.pi) / a) +
        b ^ (-sigma) / 2 := by
  have hc : 0 < t / (2 * Real.pi) := div_pos ht (by positivity)
  have he := afe_finite_sum_sub_integral_bound hsigma hc ha hab hcut hahalf
  have hphase : (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
      (n : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * Complex.I))) -
      (∫ x in a..b, (x : ℂ) ^ (-((sigma : ℂ) + (t : ℂ) * Complex.I))) =
      starRingEnd ℂ ((∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋,
        weightedWave (afePhase (t / (2 * Real.pi))) (afeWeight sigma) (n : ℝ)) -
        ∫ x in a..b, weightedWave (afePhase (t / (2 * Real.pi))) (afeWeight sigma) x) := by
    rw [map_sub, map_sum, conj_intervalIntegral]
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      have hn0 : 0 < (n : ℝ) := by
        have hf := Int.floor_nonneg.mpr ha.le
        have hn' := (Finset.mem_Ioc.mp hn).1
        exact_mod_cast (show 0 < n by omega)
      simpa only [Complex.ofReal_intCast] using (conj_weightedWave_afe sigma t hn0).symm
    · apply intervalIntegral.integral_congr
      intro x hx
      have hx0 : 0 < x := ha.trans_le ((Set.uIcc_of_le hab.le ▸ hx).1)
      exact (conj_weightedWave_afe sigma t hx0).symm
  rw [hphase, Complex.norm_conj]
  convert he using 1
  field_simp

/-- Removing the zero term gives precisely the sharp positive-integer sum, including n=1. -/
theorem sum_range_reciprocal_eq_sharpZetaSum {s : ℂ} (hs : s ≠ 0) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s) = sharpZetaSum s (N : ℝ) := by
  rw [sharpZetaSum, Nat.floor_natCast, sum_Icc_one_eq_sum_range, Finset.sum_range_succ']
  simp only [Nat.cast_zero, Complex.zero_cpow hs, div_zero, add_zero]
  apply Finset.sum_congr rfl
  intro n _
  simp only [zetaTerm, Complex.cpow_neg, one_div]

/-- The tail interval subtracts the two actual sharp positive-integer sums. -/
theorem sum_cpow_Ioc_eq_sharp_sub {a : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : a ≤ N) (s : ℂ) :
    (∑ n ∈ Finset.Ioc ⌊a⌋ (N : ℤ), (n : ℂ) ^ (-s)) =
      sharpZetaSum s (N : ℝ) - sharpZetaSum s a := by
  rw [← Int.natCast_floor_eq_floor ha]
  have he := sum_int_Ioc_eq_nat_Ioc (fun x : ℝ => (x : ℂ) ^ (-s)) ⌊a⌋₊ N
  simp only [Complex.ofReal_intCast, Complex.ofReal_natCast] at he
  rw [he, sharpZetaSum, sharpZetaSum, Nat.floor_natCast]
  have hf : ⌊a⌋₊ ≤ N := Nat.floor_le_of_le hN
  change (∑ n ∈ Finset.Ioc ⌊a⌋₊ N, zetaTerm s n) = _
  have hu : Finset.Icc 1 ⌊a⌋₊ ∪ Finset.Ioc ⌊a⌋₊ N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hd : Disjoint (Finset.Icc 1 ⌊a⌋₊) (Finset.Ioc ⌊a⌋₊ N) := by
    rw [Finset.disjoint_left]
    intro n hn hm
    have := (Finset.mem_Icc.mp hn).2
    have := (Finset.mem_Ioc.mp hm).1
    omega
  rw [← hu, Finset.sum_union hd]
  abel

/-- The exact finite power comparison tends to the sharp zeta remainder minus its pole term. -/
theorem tendsto_cpow_tail_sub_integral {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Ioc ⌊a⌋ (N : ℤ), (n : ℂ) ^ (-s)) -
      ∫ x in a..(N : ℝ), (x : ℂ) ^ (-s)) atTop
      (𝓝 (riemannZeta s - sharpZetaSum s a - (a : ℂ) ^ (1 - s) / (s - 1))) := by
  have hs0 : s ≠ 0 := by
    intro h
    simp only [h, Complex.zero_re, lt_self_iff_false] at hs
  have he := ((tendsto_regularized_sum hs hs1).sub_const (sharpZetaSum s a)).sub_const
    ((a : ℂ) ^ (1 - s) / (s - 1))
  apply he.congr'
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop a)] with N hN
  rw [sum_cpow_Ioc_eq_sharp_sub ha.le hN, integral_cpow_neg ha hN hs1,
    sum_range_reciprocal_eq_sharpZetaSum hs0]
  simp only [Complex.ofReal_natCast]
  ring

/-- The limiting Part I estimate for the actual zeta remainder, retaining its exact pole term. -/
theorem afe_zeta_sub_sum_sub_pole_bound {sigma t a : ℝ} (hsigma : 0 < sigma) (ht : 0 < t)
    (ha : 0 < a) (hcut : t / (2 * Real.pi) < a)
    (hahalf : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) :
    ‖riemannZeta ((sigma : ℂ) + (t : ℂ) * Complex.I) -
      sharpZetaSum ((sigma : ℂ) + (t : ℂ) * Complex.I) a -
      (a : ℂ) ^ (1 - ((sigma : ℂ) + (t : ℂ) * Complex.I)) /
        (((sigma : ℂ) + (t : ℂ) * Complex.I) - 1)‖ ≤
      a ^ (-sigma) / Real.pi * (1 + sigma / t) * afePartIFactor (t / (2 * Real.pi) / a) := by
  have hs : 0 < ((sigma : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hsigma
  have hs1 : (sigma : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.one_im] at him
    exact ht.ne' him
  have he := (tendsto_cpow_tail_sub_integral ha hs hs1).norm
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (-sigma) / 2) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop hsigma).comp tendsto_natCast_atTop_atTop).div_const 2
  apply le_of_tendsto_of_tendsto he
    (by simpa using hp.const_add
          (a ^ (-sigma) / Real.pi * (1 + sigma / t) * afePartIFactor (t / (2 * Real.pi) / a)))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop a)] with N hN
  have hn := afe_finite_cpow_bound hsigma.le ht ha hN hcut hahalf
  simpa only [Int.floor_natCast] using hn

/-- The pole term is at most a/t times the same sharp-cutoff weight. -/
theorem norm_afe_pole_le {sigma t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    ‖(a : ℂ) ^ (1 - ((sigma : ℂ) + (t : ℂ) * Complex.I)) /
      (((sigma : ℂ) + (t : ℂ) * Complex.I) - 1)‖ ≤ (a / t) * a ^ (-sigma) := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ha]
  have him : (((sigma : ℂ) + (t : ℂ) * Complex.I) - 1).im = t := by simp
  have hn : t ≤ ‖((sigma : ℂ) + (t : ℂ) * Complex.I) - 1‖ := by
    have he := Complex.abs_im_le_norm (((sigma : ℂ) + (t : ℂ) * Complex.I) - 1)
    rwa [him, abs_of_pos ht] at he
  have hre : (1 - ((sigma : ℂ) + (t : ℂ) * Complex.I)).re = 1 - sigma := by simp
  rw [hre]
  calc
    _ ≤ a ^ (1 - sigma) / t := div_le_div_of_nonneg_left (Real.rpow_pos_of_pos ha _).le ht hn
    _ = _ := by
      rw [sub_eq_add_neg, Real.rpow_add ha, Real.rpow_one]
      ring

end DhimanKadiriQuesadaHerrera2026
