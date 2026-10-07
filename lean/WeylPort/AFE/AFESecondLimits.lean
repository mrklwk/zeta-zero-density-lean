module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.SecondTailSharp
public import WeylPort.AFE.ZetaTruncation
public import WeylPort.AFE.WeightedIntegralAssembly

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Passing the second-order Poisson estimate to the actual AFE

The upper-cutoff limit, Gamma evaluation and lower-integral bound give a strict-strip
estimate for the actual two Dirichlet polynomials. Its explicit separate square-tail
coefficients are derived directly; the adopted general E₁ contract is in CorrectedPartII. Endpoint continuation,
source error simplification and reflected bounds remain separate obligations.
-/

namespace DhimanKadiriQuesadaHerrera2026
open Filter
open scoped Topology

/-- The source H numerator has its exact power-weight value. -/
theorem secondH_afe {σ c u : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c) (hu : 0 < u) :
    secondH (afePhase c) (afeWeight σ) u = (σ + 2 * Real.pi * c) * u ^ (-σ - 1) := by
  unfold secondH
  rw [abs_deriv_afeWeight hσ hu, (afePhase_hasDerivAt c hu).deriv,
    abs_of_nonneg (mul_nonneg (afeWeight_pos σ hu).le (div_nonneg hc hu.le))]
  unfold afeWeight
  rw [Real.rpow_sub_one hu.ne']
  ring_nf

/-- The source H₁ numerator has its exact power-weight value. -/
theorem secondH1_afe {σ c u : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c) (hu : 0 < u) :
    secondH1 (afePhase c) (afeWeight σ) u =
      (σ + 1) * (σ + 2 * Real.pi * c) * u ^ (-σ - 2) := by
  unfold secondH1
  rw [(afeWeight_deriv_hasDerivAt σ hu).deriv, (afePhase_deriv_hasDerivAt c hu).deriv,
    (afeWeight_hasDerivAt σ hu).deriv, (afePhase_hasDerivAt c hu).deriv]
  have hs1 : 0 ≤ σ + 1 := by linarith
  have hr1 := (Real.rpow_pos_of_pos hu (-σ - 1)).le
  have hr2 := (Real.rpow_pos_of_pos hu (-σ - 2)).le
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hσ hs1) hr2)]
  rw [abs_mul (afeWeight σ u), abs_of_pos (afeWeight_pos σ hu), abs_div, abs_neg,
    abs_of_nonneg hc, abs_of_nonneg (sq_nonneg u)]
  rw [abs_mul (-σ * u ^ (-σ - 1)), abs_mul (-σ), abs_neg, abs_of_nonneg hσ,
    abs_of_nonneg hr1, abs_div, abs_of_nonneg hc, abs_of_pos hu]
  unfold afeWeight
  rw [Real.rpow_sub_one hu.ne']
  have he : u ^ (-σ - 2) = u ^ (-σ) / u ^ 2 := by
    simpa only [Nat.cast_ofNat] using Real.rpow_sub_natCast hu.ne' (-σ) 2
  rw [he]
  field_simp
  ring_nf

/-- The actual H amplitude tends to zero at the upper endpoint, including σ=0. -/
theorem tendsto_secondH_afe {σ c : ℝ} (hσ : 0 ≤ σ) (hc : 0 ≤ c) :
    Tendsto (fun u : ℝ => secondH (afePhase c) (afeWeight σ) u) atTop (𝓝 0) := by
  have hs : 0 < σ + 1 := by linarith
  have ht := (tendsto_rpow_neg_atTop hs).const_mul (σ + 2 * Real.pi * c)
  apply (show Tendsto (fun u : ℝ => (σ + 2 * Real.pi * c) * u ^ (-(σ + 1))) atTop (𝓝 0) by simpa using ht).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
  rw [secondH_afe hσ hc hu]
  congr 1
  ring_nf

/-- At a natural endpoint the finite Fourier head is exactly the harmonic endpoint amplitude. -/
theorem norm_poissonHeadBoundary_nat (f g : ℝ → ℝ) (N M : ℕ) (hg : 0 ≤ g N) :
    ‖poissonHeadBoundary f g N M‖ = g N / (2 * Real.pi) * (harmonic M : ℝ) := by
  rw [norm_poissonHeadBoundary hg]
  have he : finiteS1 (N : ℝ) (M : ℝ) = (harmonic M : ℂ) := by
    simpa only [Int.cast_natCast, Nat.floor_natCast] using finiteS1_integer (N : ℤ) (M : ℝ)
  rw [he, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
  have hhm : 0 ≤ (harmonic M : ℝ) := by
    have hq : 0 ≤ harmonic M := Finset.sum_nonneg (fun n _ => by positivity)
    exact_mod_cast hq
  rw [abs_of_nonneg hhm]

/-- The full upper-endpoint error after its actual two tails are uniformly bounded. -/
noncomputable def afeSecondUpperError (σ c : ℝ) (M : ℕ) (b : ℝ) : ℝ :=
  afeWeight σ b / (2 * Real.pi) * (harmonic M : ℝ) + afeWeight σ b / 2 +
    6 * secondH (afePhase c) (afeWeight σ) b / (4 * Real.pi ^ 2)

/-- The actual upper-endpoint error vanishes for every positive σ. -/
theorem tendsto_afeSecondUpperError {σ c : ℝ} (hσ : 0 < σ) (hc : 0 ≤ c) (M : ℕ) :
    Tendsto (afeSecondUpperError σ c M) atTop (𝓝 0) := by
  have hw := tendsto_rpow_neg_atTop hσ
  have hH := tendsto_secondH_afe hσ.le hc
  have ht := (((hw.div_const (2 * Real.pi)).mul_const (harmonic M : ℝ)).add (hw.div_const 2)).add
    ((hH.const_mul 6).div_const (4 * Real.pi ^ 2))
  simp only [zero_div, zero_mul, mul_zero, add_zero] at ht
  exact ht

/-- The left-endpoint error retained in the actual AFE zeta-limit argument. -/
noncomputable def afeSecondLeftError (σ c a : ℝ) : ℝ :=
  let f : ℝ → ℝ := afePhase c
  let g : ℝ → ℝ := afeWeight σ
  let y : ℝ := c / a
  let M : ℕ := ⌊y⌋₊
  g a / (2 * Real.pi) * (Real.log 2 + 1 / y) +
    secondH f g a / (4 * Real.pi ^ 2) * ((Real.pi / 2 + Real.log 2) / y) +
    secondH1 f g a / (4 * Real.pi ^ 3) * (minusSquareBound M y + plusSquareBound y) +
    (secondH f g a * (c / a ^ 2) / (4 * Real.pi ^ 3)) * (minusCubeBound M y + plusCubeBound y)

/-- At natural upper cutoffs the actual finite AFE Poisson estimate separates the fixed left error and a vanishing upper error. -/
theorem afe_finite_poisson_second_left_half {σ c a : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c)
    (ha : 0 < a) {N : ℕ} (haN : a < (N : ℝ))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊c / a⌋₊ : ℝ) + 1 - c / a) (hsmall : c / (N : ℝ) ≤ 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ (N : ℤ), weightedWave (afePhase c) (afeWeight σ) (n : ℝ)) -
      poissonMain (afePhase c) (afeWeight σ) a N ⌊c / a⌋₊‖ ≤
        afeSecondLeftError σ c a + afeSecondUpperError σ c ⌊c / a⌋₊ N := by
  have hN := ha.trans haN
  have hya := div_pos hc ha
  have hyN := div_pos hc hN
  have heb := mul_le_mul_of_nonneg_left
    (add_le_add (norm_negativeTail_le_four (M := ⌊c / a⌋₊) hyN hsmall (N : ℝ))
      (norm_positiveTail_le_two hyN (-(N : ℝ))))
    (div_nonneg (secondH_nonneg (afePhase c) (afeWeight σ) N) (by positivity : 0 ≤ 4 * Real.pi ^ 2))
  have hea := mul_le_mul_of_nonneg_left (second_endpoint_half_integer_sharp hah hya hδ)
    (div_nonneg (secondH_nonneg (afePhase c) (afeWeight σ) a) (by positivity : 0 ≤ 4 * Real.pi ^ 2))
  have hha := norm_poissonHeadBoundary_half_integer_le (f := afePhase c) hah (afeWeight_pos σ ha).le hya
  have hhb := norm_poissonHeadBoundary_nat (afePhase c) (afeWeight σ) N ⌊c / a⌋₊ (afeWeight_pos σ hN).le
  have hg := norm_poissonBoundary_left_half_integer_le (f := afePhase c) hah (afeWeight_pos σ hN).le
  have ht := afe_finite_poisson_second_bound hσ hc ha haN
  dsimp only at ht
  rw [Int.floor_natCast, hhb] at ht
  unfold afeSecondLeftError afeSecondUpperError
  dsimp only
  simp only [div_eq_mul_inv] at ht hea heb hha hg ⊢
  nlinarith only [ht, hea, heb, hha, hg]

/-- Conjugation of the actual finite Poisson main term gives precisely the weighted Dirichlet integrals. -/
theorem conj_poissonMain_afe (σ t : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (M : ℕ) :
    starRingEnd ℂ (poissonMain (afePhase (t / (2 * Real.pi))) (afeWeight σ) a b M) =
      ∑ m ∈ Finset.Icc 0 M, weightedIntegral ((σ : ℂ) + (t : ℂ) * Complex.I) a b m := by
  unfold poissonMain
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [conj_intervalIntegral]
  unfold weightedIntegral
  apply intervalIntegral.integral_congr
  intro u hu
  have hup : 0 < u := ha.trans_le ((Set.uIcc_of_le hab ▸ hu).1)
  dsimp only
  rw [map_mul, conj_weightedWave_afe σ t hup, conj_expMode]
  congr 1
  unfold expMode
  congr 1
  push_cast
  ring

/-- Separating the zero mode retains the actual unweighted Dirichlet integral and every positive frequency. -/
theorem sum_weightedIntegral_eq_zero_add (s : ℂ) (a b : ℝ) (M : ℕ) :
    (∑ m ∈ Finset.Icc 0 M, weightedIntegral s a b m) =
      (∫ u in a..b, (u : ℂ) ^ (-s)) + ∑ m ∈ Finset.Icc 1 M, weightedIntegral s a b m := by
  have hset : Finset.Icc 0 M = Finset.range (M + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hset, Finset.sum_range_succ', sum_Icc_one_eq_sum_range]
  simp only [Nat.cast_zero, weightedIntegral, Complex.ofReal_zero, mul_zero, zero_mul,
    Complex.exp_zero, mul_one]
  rw [add_comm]

/-- The actual AFE finite Poisson bound in principal complex-power form, with the full positive integral head retained. -/
theorem afe_second_finite_cpow_bound {σ t a : ℝ} (hσ : 0 ≤ σ) (ht : 0 < t)
    (ha : 0 < a) {N : ℕ} (haN : a < (N : ℝ))
    (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊(t / (2 * Real.pi)) / a⌋₊ : ℝ) + 1 - (t / (2 * Real.pi)) / a)
    (hsmall : (t / (2 * Real.pi)) / (N : ℝ) ≤ 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ (N : ℤ), (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) -
      ∑ m ∈ Finset.Icc 0 ⌊(t / (2 * Real.pi)) / a⌋₊,
        weightedIntegral ((σ : ℂ) + (t : ℂ) * Complex.I) a N m‖ ≤
      afeSecondLeftError σ (t / (2 * Real.pi)) a +
        afeSecondUpperError σ (t / (2 * Real.pi)) ⌊(t / (2 * Real.pi)) / a⌋₊ N := by
  have hc : 0 < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hb := afe_finite_poisson_second_left_half hσ hc ha haN hah hδ hsmall
  have he : (∑ n ∈ Finset.Ioc ⌊a⌋ (N : ℤ), (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) -
      ∑ m ∈ Finset.Icc 0 ⌊(t / (2 * Real.pi)) / a⌋₊,
        weightedIntegral ((σ : ℂ) + (t : ℂ) * Complex.I) a N m =
      starRingEnd ℂ ((∑ n ∈ Finset.Ioc ⌊a⌋ (N : ℤ),
        weightedWave (afePhase (t / (2 * Real.pi))) (afeWeight σ) (n : ℝ)) -
        poissonMain (afePhase (t / (2 * Real.pi))) (afeWeight σ) a N ⌊(t / (2 * Real.pi)) / a⌋₊) := by
    rw [map_sub, map_sum, conj_poissonMain_afe σ t ha haN.le]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 < (n : ℝ) := by
      have hf := Int.floor_nonneg.mpr ha.le
      have hn' := (Finset.mem_Ioc.mp hn).1
      exact_mod_cast (show 0 < n by omega)
    simpa only [Complex.ofReal_intCast] using (conj_weightedWave_afe σ t hn0).symm
  rw [he, Complex.norm_conj]
  exact hb

/-- The second-order finite Poisson estimate passes to the actual zeta remainder and positive improper integrals. -/
theorem afe_zeta_sub_sum_pole_integrals_bound {σ t a : ℝ} (hσ : σ ∈ Set.Ioo 0 1) (ht : 0 < t)
    (ha : 0 < a) (hah : ∃ k : ℤ, a = (k : ℝ) + 1 / 2)
    (hδ : 1 / 2 ≤ (⌊(t / (2 * Real.pi)) / a⌋₊ : ℝ) + 1 - (t / (2 * Real.pi)) / a) :
    let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    let c : ℝ := t / (2 * Real.pi)
    ‖riemannZeta s - sharpZetaSum s a - (a : ℂ) ^ (1 - s) / (s - 1) -
      ∑ m ∈ Finset.Icc 1 ⌊c / a⌋₊, weightedIntegralTail s a m‖ ≤ afeSecondLeftError σ c a := by
  dsimp only
  have hc : 0 < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hs : 0 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ.1
  have hs1 : (σ : ℂ) + (t : ℂ) * Complex.I ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.one_im] at him
    exact ht.ne' him
  have hJ : Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc 1 ⌊(t / (2 * Real.pi)) / a⌋₊,
      weightedIntegral ((σ : ℂ) + (t : ℂ) * Complex.I) a N m) atTop
      (𝓝 (∑ m ∈ Finset.Icc 1 ⌊(t / (2 * Real.pi)) / a⌋₊,
        weightedIntegralTail ((σ : ℂ) + (t : ℂ) * Complex.I) a m)) := by
    apply tendsto_finsetSum
    intro m hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    exact (weightedIntegral_tendsto_tail hσ hm0 a).comp tendsto_natCast_atTop_atTop
  have hleft := ((tendsto_cpow_tail_sub_integral ha hs hs1).sub hJ).norm
  have hright := ((tendsto_afeSecondUpperError hσ.1 hc.le ⌊(t / (2 * Real.pi)) / a⌋₊).comp
    tendsto_natCast_atTop_atTop).const_add (afeSecondLeftError σ (t / (2 * Real.pi)) a)
  apply le_of_tendsto_of_tendsto hleft (by simpa only [add_zero] using hright)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_gt_atTop (max a (2 * (t / (2 * Real.pi)))))] with N hN
  have haN : a < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hNpos : 0 < (N : ℝ) := ha.trans haN
  have hsmall : (t / (2 * Real.pi)) / (N : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hNpos).mpr
    have htN := (le_max_right a (2 * (t / (2 * Real.pi)))).trans_lt hN
    linarith
  have hb := afe_second_finite_cpow_bound hσ.1.le ht ha haN hah hδ hsmall
  rw [sum_weightedIntegral_eq_zero_add] at hb
  simpa only [sub_add_eq_sub_sub, Function.comp_apply] using hb

/-- The actual integral tails beginning at x approximate the dual polynomial, retaining the full lower-integral and Gamma errors. -/
theorem norm_sum_weightedIntegralTail_from_x_sub_chi_le {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Ioo 0 1) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖(∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * Complex.I) x (m : ℝ)) -
      chi ((σ : ℂ) + (t : ℂ) * Complex.I) *
        ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * Complex.I) - 1)‖ ≤
      ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        (Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))) *
        (y ^ σ * Real.log y + 1) +
      x ^ (-σ) * (Real.log y / Real.pi +
        (Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2) / Real.pi +
          3 / (4 * Real.pi * y) + 3 / (8 * Real.pi * y ^ 2)) := by
  have he : (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * Complex.I) x (m : ℝ)) =
      (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * Complex.I) 0 (m : ℝ)) -
        ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegral ((σ : ℂ) + (t : ℂ) * Complex.I) 0 x (m : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    exact weightedIntegralTail_eq_sub hσ (by exact_mod_cast (Finset.mem_Icc.mp hm).1) x
  rw [he, sub_right_comm]
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_sum_weightedIntegralTail_sub_chi_le hσ hy ht₀ ht)
    (norm_sum_lower_integral_source hσ.2 hx hy hscale hxhalf hyhalf))

/-- The actual sharp two-polynomial AFE on the strict strip, with the proved Poisson, pole, Gamma and lower-integral errors kept explicit. -/
theorem afe_strict_strip_bound {σ t x y t₀ : ℝ}
    (hσ : σ ∈ Set.Ioo 0 1) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = t)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    ‖afeRemainder ((σ : ℂ) + (t : ℂ) * Complex.I) x y‖ ≤
      afeSecondLeftError σ (t / (2 * Real.pi)) x + (x / t) * x ^ (-σ) +
      ‖chi ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        (Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))) * (y ^ σ * Real.log y + 1) +
      x ^ (-σ) * (Real.log y / Real.pi +
        (Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2) / Real.pi +
          3 / (4 * Real.pi * y) + 3 / (8 * Real.pi * y ^ 2)) := by
  have htpos := ht₀.trans_le ht
  have hxpos : 0 < x := by linarith
  have hcy : (t / (2 * Real.pi)) / x = y := by
    rw [← hscale]
    field_simp
  have hδ : 1 / 2 ≤ (⌊(t / (2 * Real.pi)) / x⌋₊ : ℝ) + 1 - (t / (2 * Real.pi)) / x := by
    rw [hcy]
    obtain ⟨k, hk⟩ := hyhalf
    have he := half_integer_eq_nat_floor_add_half hy k hk
    linarith
  have hz := afe_zeta_sub_sum_pole_integrals_bound hσ htpos hxpos hxhalf hδ
  dsimp only at hz
  rw [hcy] at hz
  have hJ := norm_sum_weightedIntegralTail_from_x_sub_chi_le (t := t) hσ hx hy hxhalf hyhalf
    (by simpa only [abs_of_pos htpos] using hscale) ht₀ (by simpa only [abs_of_pos htpos] using ht)
  have hp := norm_afe_pole_le (sigma := σ) htpos hxpos
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hpoly : sharpZetaSum (1 - s) y = ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (s - 1) := by
    simp only [sharpZetaSum, zetaTerm, neg_sub]
  have he : afeRemainder s x y =
      (riemannZeta s - sharpZetaSum s x - (x : ℂ) ^ (1 - s) / (s - 1) -
        ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail s x m) +
      ((∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail s x m) -
        chi s * ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (s - 1)) +
      (x : ℂ) ^ (1 - s) / (s - 1) := by
    unfold afeRemainder
    rw [hpoly]
    ring
  change ‖afeRemainder s x y‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) (le_refl _)).trans
  have hb := add_le_add (add_le_add hz hJ) hp
  dsimp only [s]
  linarith only [hb]

end DhimanKadiriQuesadaHerrera2026
