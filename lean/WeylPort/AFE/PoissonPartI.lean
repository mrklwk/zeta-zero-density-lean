module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.EulerMaclaurin

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Assembly of the corrected weighted Poisson formula, Part I -/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory

/-- The finite endpoint expression obtained by integrating the stationary frequency head. -/
noncomputable def poissonHeadBoundary (f g : ℝ → ℝ) (x : ℝ) (M : ℕ) : ℂ :=
  weightedWave f g x / (2 * Real.pi * Complex.I) * finiteS1 x M

/-- The actual finite sum of Fourier integrals from zero through M. -/
noncomputable def poissonMain (f g : ℝ → ℝ) (a b : ℝ) (M : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 M, ∫ x in a..b, weightedWave f g x * expMode x n

/-- The actual negative Fourier mode has its stated derivative. -/
theorem hasDerivAt_expMode (n : ℕ) (x : ℝ) :
    HasDerivAt (fun u => expMode u n)
      ((-2 * Real.pi * Complex.I * n) * expMode x n) x := by
  have he : (fun u : ℝ => expMode u n) =
      fun u : ℝ => Complex.exp ((-2 * Real.pi * Complex.I * n) * (u : ℂ)) := by
    funext u
    unfold expMode
    congr 1
    push_cast
    ring
  rw [he]
  have ht := ((hasDerivAt_id x).ofReal_comp.const_mul
    (-2 * (Real.pi : ℂ) * Complex.I * n)).cexp
  rw [congrFun he x]
  simp only [id_eq, Complex.ofReal_one, mul_one] at ht
  convert ht using 1
  ring

/-- The regularity hypotheses provide the exact derivative of the source wave on the interval. -/
theorem PartIRegularity.wave_hasDerivAt {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (x : ℝ) (hx : x ∈ Set.uIcc a b) :
    HasDerivAt (weightedWave f g) (waveDerivative f g x) x := by
  rw [Set.uIcc_of_le h.lt.le] at hx
  unfold weightedWave waveDerivative
  simpa only [Complex.ofReal_mul, mul_assoc] using
    weighted_wave_hasDerivAt (h.f_differentiable x hx) (h.g_differentiable x hx)

/-- Integration by parts for one actual frequency in the finite head. -/
theorem negativeCoefficient_eq_boundary_add_integral {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) {n : ℕ} (hn : 0 < n) :
    negativeCoefficient f g a b n =
      weightedWave f g b * expMode b n / (2 * Real.pi * Complex.I * n) -
      weightedWave f g a * expMode a n / (2 * Real.pi * Complex.I * n) +
        ∫ x in a..b, weightedWave f g x * expMode x n := by
  have hm : Continuous (fun x => (-2 * Real.pi * Complex.I * (n : ℂ)) * expMode x n) := by
    unfold expMode
    fun_prop
  have hi : IntervalIntegrable (waveDerivative f g) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h.lt.le]
    exact h.waveDerivative_continuous
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x _ => hasDerivAt_expMode n x) h.wave_hasDerivAt (hm.intervalIntegrable a b) hi
  have he1 : (fun x => expMode x n * waveDerivative f g x) =
      fun x => waveDerivative f g x * expMode x n := by funext x; ring
  have he2 : (fun x => (-2 * Real.pi * Complex.I * (n : ℂ) * expMode x n) * weightedWave f g x) =
      fun x => (-2 * Real.pi * Complex.I * (n : ℂ)) * (weightedWave f g x * expMode x n) := by
    funext x
    ring
  rw [he1, integral_waveDerivative_expMode, he2, intervalIntegral.integral_const_mul] at hb
  unfold negativeCoefficient
  rw [hb]
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

/-- The finite endpoint expression is exactly the sum of the endpoint Fourier coefficients. -/
theorem poissonHeadBoundary_eq_sum (f g : ℝ → ℝ) (x : ℝ) (M : ℕ) :
    poissonHeadBoundary f g x M =
      ∑ n ∈ Finset.Icc 1 M, weightedWave f g x * expMode x n / (2 * Real.pi * Complex.I * n) := by
  unfold poissonHeadBoundary finiteS1
  rw [Nat.floor_natCast, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- All finite-head integrations by parts assemble with their actual complex endpoint terms. -/
theorem sum_negativeCoefficient_head {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (M : ℕ) :
    (∑ n ∈ Finset.Icc 1 M, negativeCoefficient f g a b n) =
      poissonHeadBoundary f g b M - poissonHeadBoundary f g a M +
        ∑ n ∈ Finset.Icc 1 M, ∫ x in a..b, weightedWave f g x * expMode x n := by
  rw [poissonHeadBoundary_eq_sum, poissonHeadBoundary_eq_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact negativeCoefficient_eq_boundary_add_integral h (by
    have := (Finset.mem_Icc.mp hn).1
    omega)


/-- Separating the zero frequency gives exactly the main integral plus the positive head. -/
theorem poissonMain_eq_zero_add_head (f g : ℝ → ℝ) (a b : ℝ) (M : ℕ) :
    poissonMain f g a b M = (∫ x in a..b, weightedWave f g x) +
      ∑ n ∈ Finset.Icc 1 M, ∫ x in a..b, weightedWave f g x * expMode x n := by
  have hset : Finset.Icc 0 M = Finset.range (M + 1) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [poissonMain, hset, Finset.sum_range_succ', sum_Icc_one_eq_sum_range]
  simp only [expMode, Nat.cast_zero, mul_zero, zero_mul, Complex.ofReal_zero,
    Complex.exp_zero, mul_one]
  rw [add_comm]

/-- Absolute convergence permits the exact finite-head and infinite-tail decomposition. -/
theorem negativeCoefficient_sum_eq_head_add_tail {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (M : ℕ) :
    (∑' n, negativeCoefficient f g a b n) =
      (∑ n ∈ Finset.Icc 1 M, negativeCoefficient f g a b n) +
        ∑' n : ℕ, negativeCoefficient f g a b (n + M + 1) := by
  have he := (summable_negativeCoefficient h).sum_add_tsum_nat_add (M + 1)
  rw [Finset.sum_range_succ', ← sum_Icc_one_eq_sum_range] at he
  simpa only [negativeCoefficient, Nat.cast_zero, mul_zero, div_zero, add_zero,
    Nat.add_assoc] using he.symm

/-- Exact truncated Poisson identity with the actual main sum and both infinite tails. -/
theorem weighted_sum_eq_poissonMain_add_remainder {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (M : ℕ) :
    (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M =
      poissonHeadBoundary f g b M - poissonHeadBoundary f g a M +
        (∑' n : ℕ, negativeCoefficient f g a b (n + M + 1)) -
          (∑' n, positiveCoefficient f g a b n) + poissonBoundary f g a b := by
  rw [weighted_sum_eq_fourier h, negativeCoefficient_sum_eq_head_add_tail h M,
    sum_negativeCoefficient_head h M, poissonMain_eq_zero_add_head]
  ring

/-- The completed general-endpoint convention uses the exact harmonic value at integers. -/
noncomputable def poissonEndpointMajorant (x y : ℝ) : ℝ := by
  classical
  exact if ∃ k : ℤ, x = (k : ℝ) then (harmonic ⌊y⌋₊ : ℝ) else tildeS1 x y

/-- The general endpoint majorant bounds the actual finite sum, including integer endpoints. -/
theorem norm_finiteS1_le_poissonEndpointMajorant (x y : ℝ) :
    ‖finiteS1 x y‖ ≤ poissonEndpointMajorant x y := by
  classical
  unfold poissonEndpointMajorant
  split_ifs with hx
  · obtain ⟨k, rfl⟩ := hx
    rw [finiteS1_integer, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by
        have hh : 0 ≤ harmonic ⌊y⌋₊ := Finset.sum_nonneg (fun n _ => by positivity)
        exact_mod_cast hh)]
  · exact norm_finiteS1_le_tildeS1 (fun k hk => hx ⟨k, hk⟩)

/-- The finite endpoint expression has precisely the expected amplitude times S₁ norm. -/
theorem norm_poissonHeadBoundary {f g : ℝ → ℝ} {x : ℝ} (hg : 0 ≤ g x) (M : ℕ) :
    ‖poissonHeadBoundary f g x M‖ = g x / (2 * Real.pi) * ‖finiteS1 x M‖ := by
  rw [poissonHeadBoundary, norm_mul, norm_div, norm_weightedWave hg]
  congr 2
  simp

/-- The endpoint bound uses y itself, exactly as in the final source statement. -/
theorem norm_poissonHeadBoundary_le {f g : ℝ → ℝ} {x y : ℝ} (hg : 0 ≤ g x) :
    ‖poissonHeadBoundary f g x ⌊y⌋₊‖ ≤ g x / (2 * Real.pi) * poissonEndpointMajorant x y := by
  rw [norm_poissonHeadBoundary hg]
  have he : finiteS1 x (⌊y⌋₊ : ℝ) = finiteS1 x y := by simp only [finiteS1, Nat.floor_natCast]
  rw [he]
  exact mul_le_mul_of_nonneg_left (norm_finiteS1_le_poissonEndpointMajorant x y) (by positivity)


/-- The complete logarithmic and digamma part of the corrected N = 0 remainder. -/
noncomputable def partIAnalyticError (f g : ℝ → ℝ) (a : ℝ) : ℝ :=
  (partICoefficient f g a / deriv f a) *
    (Real.log (1 + deriv f a) + Real.eulerMascheroniConstant + Real.log ((⌊deriv f a⌋₊ : ℝ) + 1) -
      (Complex.digamma ((⌊deriv f a⌋₊ : ℝ) + 1 - deriv f a : ℝ)).re -
        1 / (2 * ((⌊deriv f a⌋₊ : ℝ) + 1)) - 1 / (2 * (1 + deriv f a)))

/-- The complete N = 0 remainder, retaining both finite endpoint terms and the actual G. -/
noncomputable def partIZeroError (f g : ℝ → ℝ) (a b : ℝ) : ℝ :=
  partIAnalyticError f g a +
    (g b * poissonEndpointMajorant b (deriv f a) + g a * poissonEndpointMajorant a (deriv f a)) /
      (2 * Real.pi) + ‖poissonBoundary f g a b‖

/-- The corrected weighted Part I estimate at N = 0 for arbitrary real endpoints. -/
theorem corrected_poisson_partI_zero {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      poissonMain f g a b ⌊deriv f a⌋₊‖ ≤ partIZeroError f g a b := by
  rw [weighted_sum_eq_poissonMain_add_remainder h]
  have ht := norm_negativeCoefficient_tail_le_source h (Nat.lt_floor_add_one (deriv f a))
  have hp := norm_positiveCoefficient_sum_le_source h
  have ha := norm_poissonHeadBoundary_le (f := f) (y := deriv f a)
    (h.g_nonneg a (Set.left_mem_Icc.mpr h.lt.le))
  have hb := norm_poissonHeadBoundary_le (f := f) (y := deriv f a)
    (h.g_nonneg b (Set.right_mem_Icc.mpr h.lt.le))
  have htri (A B T P E : ℂ) : ‖A - B + T - P + E‖ ≤ ‖A‖ + ‖B‖ + ‖T‖ + ‖P‖ + ‖E‖ := by
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_sub_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)) le_rfl)
  apply (htri _ _ _ _ _).trans
  have hsum := add_le_add (add_le_add (add_le_add (add_le_add hb ha) ht) hp)
    (le_refl ‖poissonBoundary f g a b‖)
  convert hsum using 1
  unfold partIZeroError partIAnalyticError
  ring

/-- The main Fourier integral sum is the source's literal phase expression. -/
theorem poissonMain_eq_source (f g : ℝ → ℝ) (a b : ℝ) (M : ℕ) :
    poissonMain f g a b M = ∑ n ∈ Finset.Icc 0 M,
      ∫ x in a..b, (g x : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * ((f x - (n : ℝ) * x : ℝ) : ℂ)) := by
  unfold poissonMain
  apply Finset.sum_congr rfl
  intro n _
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  unfold weightedWave expMode
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- Away from integers the completed endpoint convention is exactly the printed tilde-S₁. -/
theorem poissonEndpointMajorant_eq_tildeS1 {x : ℝ} (hx : ∀ k : ℤ, x ≠ (k : ℝ)) (y : ℝ) :
    poissonEndpointMajorant x y = tildeS1 x y := by
  classical
  simp only [poissonEndpointMajorant, not_exists.mpr hx, ↓reduceIte]

/-- The finite harmonic endpoint term has the printed half-integer bound even below cutoff one. -/
theorem norm_finiteS1_half_integer_le_of_pos (k : ℤ) {y : ℝ} (hy : 0 < y) :
    ‖finiteS1 ((k : ℝ) + 1 / 2) y‖ ≤ Real.log 2 + 1 / y := by
  by_cases hy1 : 1 ≤ y
  · exact norm_finiteS1_half_integer_le k hy1
  · rw [(finite_sums_eq_zero (x := (k : ℝ) + 1 / 2) (lt_of_not_ge hy1)).2, norm_zero]
    positivity


/-- The source's improved finite endpoint bound at a half-integer. -/
theorem norm_poissonHeadBoundary_half_integer_le {f g : ℝ → ℝ} {x y : ℝ}
    (hx : ∃ k : ℤ, x = (k : ℝ) + 1 / 2) (hg : 0 ≤ g x) (hy : 0 < y) :
    ‖poissonHeadBoundary f g x ⌊y⌋₊‖ ≤
      g x / (2 * Real.pi) * (Real.log 2 + 1 / y) := by
  rw [norm_poissonHeadBoundary hg]
  have he : finiteS1 x (⌊y⌋₊ : ℝ) = finiteS1 x y := by simp only [finiteS1, Nat.floor_natCast]
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  obtain ⟨k, rfl⟩ := hx
  exact norm_finiteS1_half_integer_le_of_pos k hy

/-- Corrected Part I's full half-integer N = 0 estimate, including its log(2) refinement. -/
theorem corrected_poisson_partI_zero_half_integer {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b)
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      poissonMain f g a b ⌊deriv f a⌋₊‖ ≤
        partIAnalyticError f g a + (g a + g b) / (2 * Real.pi) * (Real.log 2 + 1 / deriv f a) := by
  rw [weighted_sum_eq_poissonMain_add_remainder h]
  have ht := norm_negativeCoefficient_tail_le_source h (Nat.lt_floor_add_one (deriv f a))
  have hp := norm_positiveCoefficient_sum_le_source h
  have hy := h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)
  have hea := norm_poissonHeadBoundary_half_integer_le (f := f) ha
    (h.g_nonneg a (Set.left_mem_Icc.mpr h.lt.le)) hy
  have heb := norm_poissonHeadBoundary_half_integer_le (f := f) hb
    (h.g_nonneg b (Set.right_mem_Icc.mpr h.lt.le)) hy
  have he : poissonBoundary f g a b = 0 := by
    obtain ⟨k, rfl⟩ := ha
    obtain ⟨l, rfl⟩ := hb
    exact poissonBoundary_half_integer f g k l
  rw [he, add_zero]
  have htri (A B T P : ℂ) : ‖A - B + T - P‖ ≤ ‖A‖ + ‖B‖ + ‖T‖ + ‖P‖ := by
    exact (norm_sub_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)
  apply (htri _ _ _ _).trans
  have hsum := add_le_add (add_le_add (add_le_add heb hea) ht) hp
  convert hsum using 1
  unfold partIAnalyticError
  ring

/-- The unchanged generic sine-denominator form is valid at all noninteger endpoints. -/
theorem corrected_poisson_partI_zero_noninteger {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b)
    (ha : ∀ k : ℤ, a ≠ (k : ℝ)) (hb : ∀ k : ℤ, b ≠ (k : ℝ)) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      poissonMain f g a b ⌊deriv f a⌋₊‖ ≤ partIAnalyticError f g a +
        (g b * tildeS1 b (deriv f a) + g a * tildeS1 a (deriv f a)) / (2 * Real.pi) +
          ‖poissonBoundary f g a b‖ := by
  have he := corrected_poisson_partI_zero h
  simpa only [partIZeroError, poissonEndpointMajorant_eq_tildeS1 ha,
    poissonEndpointMajorant_eq_tildeS1 hb] using he

end DhimanKadiriQuesadaHerrera2026
