module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.SecondCoefficients
public import WeylPort.AFE.PartIISignReview

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Actual H/H₁ assembly and AFE finite Poisson error

The two square coefficients stay separate in the AFE bound.
The E₁ equality implements the square-tail correction proved in PartIISignReview.
The E₂ coefficient is unchanged from the frozen source.
-/

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory

/-- The literal square-denominator coefficient in the positive-frequency source estimate. -/
noncomputable def plusSquareBound (y : ℝ) : ℝ :=
  (Real.log (y + 1) + Real.eulerMascheroniConstant) / y ^ 2 -
    (1 + 2 * y) / (2 * y ^ 2 * (y + 1))

/-- The literal cube-denominator coefficient in the positive-frequency source estimate. -/
noncomputable def plusCubeBound (y : ℝ) : ℝ :=
  (Real.log (y + 1) + Real.eulerMascheroniConstant) / y ^ 3 -
    (1 + 3 * y + 3 * y ^ 2) / (2 * y ^ 3 * (y + 1) ^ 2)

/-- The actual positive-frequency endpoint expression for one amplitude. -/
noncomputable def positiveModeError (p p' h h' : ℝ → ℝ) (a b : ℝ) : ℝ :=
  |h b| / (4 * Real.pi ^ 2) * ‖positiveTail (-b) (p b)‖ +
  |h a| / (4 * Real.pi ^ 2) * ‖positiveTail (-a) (p a)‖ +
  (|h' a| / (4 * Real.pi ^ 3)) * plusSquareBound (p a) +
  (|h a * p' a| / (4 * Real.pi ^ 3)) * plusCubeBound (p a)

/-- The complete source H numerator, evaluated on the actual phase and weight. -/
noncomputable def secondH (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  |deriv g x| + 2 * Real.pi * |g x * deriv f x|

/-- The complete source H₁ numerator, evaluated on the actual derivatives. -/
noncomputable def secondH1 (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  |deriv (deriv g) x| + 2 * Real.pi *
    (|g x * deriv (deriv f) x| + |deriv g x * deriv f x|)

/-- The square coefficient is nonnegative because it bounds a nonnegative actual series. -/
theorem plusSquareBound_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ plusSquareBound y :=
  (tsum_nonneg (fun n : ℕ => by positivity : ∀ n : ℕ,
    0 ≤ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ 2))).trans (harmonic_plus_square_bound hy)

/-- The cube coefficient is nonnegative because it bounds a nonnegative actual series. -/
theorem plusCubeBound_nonneg {y : ℝ} (hy : 0 < y) : 0 ≤ plusCubeBound y :=
  (tsum_nonneg (fun n : ℕ => by positivity : ∀ n : ℕ,
    0 ≤ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ 3))).trans (harmonic_plus_cube_bound hy)

/-- Combining the two amplitude majorants yields exactly the source H/H₁ terms. -/
theorem positiveModeError_pair_le {f g : ℝ → ℝ} {a b : ℝ}
    (hfa : 0 < deriv f a) (hfd : DifferentiableAt ℝ (deriv f) a)
    (hgd : DifferentiableAt ℝ g a) :
    positiveModeError (deriv f) (deriv (deriv f)) (deriv g) (deriv (deriv g)) a b +
      2 * Real.pi * positiveModeError (deriv f) (deriv (deriv f))
        (fun u => g u * deriv f u) (deriv (fun u => g u * deriv f u)) a b ≤
      secondH f g b / (4 * Real.pi ^ 2) * ‖positiveTail (-b) (deriv f b)‖ +
      secondH f g a / (4 * Real.pi ^ 2) * ‖positiveTail (-a) (deriv f a)‖ +
      secondH1 f g a / (4 * Real.pi ^ 3) * plusSquareBound (deriv f a) +
      (secondH f g a * |deriv (deriv f) a| / (4 * Real.pi ^ 3)) * plusCubeBound (deriv f a) := by
  have hd : deriv (fun u => g u * deriv f u) a =
      deriv g a * deriv f a + g a * deriv (deriv f) a :=
    (hgd.hasDerivAt.mul hfd.hasDerivAt).deriv
  have hb := abs_add_le (deriv g a * deriv f a) (g a * deriv (deriv f) a)
  have hc : 0 ≤ 2 * Real.pi / (4 * Real.pi ^ 3) * plusSquareBound (deriv f a) :=
    mul_nonneg (by positivity) (plusSquareBound_nonneg hfa)
  have ht := mul_le_mul_of_nonneg_right hb hc
  unfold positiveModeError secondH secondH1
  rw [hd]
  simp only [abs_mul] at ht ⊢
  simp only [div_eq_mul_inv] at ht ⊢
  nlinarith only [ht]

/-- The exact positive coefficient identity transfers proved bounds on the two actual amplitude series. -/
theorem norm_positiveCoefficient_le_mode_errors {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b)
    (hg : Summable (secondModeTerm f (deriv g) a b))
    (hgf : Summable (secondModeTerm f (fun u => g u * deriv f u) a b))
    (bg : ‖∑' n : ℕ, secondModeTerm f (deriv g) a b n‖ ≤
      positiveModeError (deriv f) (deriv (deriv f)) (deriv g) (deriv (deriv g)) a b)
    (bgf : ‖∑' n : ℕ, secondModeTerm f (fun u => g u * deriv f u) a b n‖ ≤
      positiveModeError (deriv f) (deriv (deriv f))
        (fun u => g u * deriv f u) (deriv (fun u => g u * deriv f u)) a b)
    (hfd : DifferentiableAt ℝ (deriv f) a) :
    ‖∑' n : ℕ, positiveCoefficient f g a b n‖ ≤
      secondH f g b / (4 * Real.pi ^ 2) * ‖positiveTail (-b) (deriv f b)‖ +
      secondH f g a / (4 * Real.pi ^ 2) * ‖positiveTail (-a) (deriv f a)‖ +
      secondH1 f g a / (4 * Real.pi ^ 3) * plusSquareBound (deriv f a) +
      (secondH f g a * |deriv (deriv f) a| / (4 * Real.pi ^ 3)) * plusCubeBound (deriv f a) := by
  rw [tsum_positiveCoefficient_eq_secondModes h hg hgf]
  apply (norm_add_le _ _).trans
  rw [norm_div, Complex.norm_I, div_one, norm_mul]
  have hc : ‖2 * (Real.pi : ℂ)‖ = 2 * Real.pi := by simp
  rw [hc]
  exact (add_le_add bg (mul_le_mul_of_nonneg_left bgf (by positivity))).trans
    (positiveModeError_pair_le (h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)) hfd
      (h.g_differentiable a (Set.left_mem_Icc.mpr h.lt.le)))

/-- The actual AFE positive Poisson tail satisfies the complete H/H₁ bound, with all integral estimates derived. -/
theorem afe_positiveCoefficient_bound {σ c a b : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) :
    ‖∑' n : ℕ, positiveCoefficient (afePhase c) (afeWeight σ) a b n‖ ≤
      secondH (afePhase c) (afeWeight σ) b / (4 * Real.pi ^ 2) * ‖positiveTail (-b) (c / b)‖ +
      secondH (afePhase c) (afeWeight σ) a / (4 * Real.pi ^ 2) * ‖positiveTail (-a) (c / a)‖ +
      secondH1 (afePhase c) (afeWeight σ) a / (4 * Real.pi ^ 3) * plusSquareBound (c / a) +
      (secondH (afePhase c) (afeWeight σ) a * (c / a ^ 2) / (4 * Real.pi ^ 3)) * plusCubeBound (c / a) := by
  have hr := afe_partIRegularity hσ hc ha hab
  have hg := afe_positive_second_tail_bound hσ hc ha hab (deriv (afeWeight σ)) (Or.inl rfl)
  have hgf := afe_positive_second_tail_bound hσ hc ha hab
    (fun u => afeWeight σ u * deriv (afePhase c) u) (Or.inr rfl)
  have hn := norm_positiveCoefficient_le_mode_errors hr hg.1 hgf.1
    (show ‖∑' n : ℕ, secondModeTerm (afePhase c) (deriv (afeWeight σ)) a b n‖ ≤
      positiveModeError (deriv (afePhase c)) (deriv (deriv (afePhase c)))
        (deriv (afeWeight σ)) (deriv (deriv (afeWeight σ))) a b by
      simpa only [positiveModeError, plusSquareBound, plusCubeBound,
        (afePhase_hasDerivAt c ha).deriv, (afePhase_hasDerivAt c (ha.trans hab)).deriv,
        (afePhase_deriv_hasDerivAt c ha).deriv] using hg.2)
    (show ‖∑' n : ℕ, secondModeTerm (afePhase c) (fun u => afeWeight σ u * deriv (afePhase c) u) a b n‖ ≤
      positiveModeError (deriv (afePhase c)) (deriv (deriv (afePhase c)))
        (fun u => afeWeight σ u * deriv (afePhase c) u)
        (deriv (fun u => afeWeight σ u * deriv (afePhase c) u)) a b by
      simpa only [positiveModeError, plusSquareBound, plusCubeBound,
        (afePhase_hasDerivAt c ha).deriv, (afePhase_hasDerivAt c (ha.trans hab)).deriv,
        (afePhase_deriv_hasDerivAt c ha).deriv] using hgf.2)
    (afePhase_deriv_hasDerivAt c ha).differentiableAt
  simpa only [(afePhase_hasDerivAt c ha).deriv, (afePhase_hasDerivAt c (ha.trans hab)).deriv,
    (afePhase_deriv_hasDerivAt c ha).deriv, abs_div, abs_neg, abs_of_pos hc,
    abs_of_nonneg (sq_nonneg a)] using hn

/-- The literal square-denominator coefficient in the upper-frequency source estimate. -/
noncomputable def minusSquareBound (M : ℕ) (y : ℝ) : ℝ :=
  let δ : ℝ := (M : ℝ) + 1 - y
  (1 / δ ^ 2 + 1 / (δ + 1) ^ 2 + 1 / (δ + 1)) / y -
    (Real.log ((M : ℝ) + 1) - 1 / ((M : ℝ) + 1) - (Complex.digamma (δ : ℂ)).re) / y ^ 2

/-- The literal cube-denominator coefficient in the upper-frequency source estimate. -/
noncomputable def minusCubeBound (M : ℕ) (y : ℝ) : ℝ :=
  let δ : ℝ := (M : ℝ) + 1 - y
  (1 / δ ^ 3 + 1 / (δ + 1) ^ 3 + 1 / (2 * (δ + 1) ^ 2)) / y -
    (1 / δ ^ 2 + 1 / (δ + 1)) / y ^ 2 +
    (Real.log ((M : ℝ) + 1) - 1 / (2 * ((M : ℝ) + 1)) - (Complex.digamma (δ : ℂ)).re) / y ^ 3

/-- The complete upper-frequency majorant for one actual amplitude. -/
noncomputable def negativeModeError (p p' h h' : ℝ → ℝ) (a b : ℝ) (M : ℕ) : ℝ :=
  |h b| / (4 * Real.pi ^ 2) * ‖negativeTail M b (p b)‖ +
  |h a| / (4 * Real.pi ^ 2) * ‖negativeTail M a (p a)‖ +
  (|h' a| / (4 * Real.pi ^ 3)) * minusSquareBound M (p a) +
  (|h a * p' a| / (4 * Real.pi ^ 3)) * minusCubeBound M (p a)

/-- The upper square coefficient is nonnegative because it bounds the actual positive series. -/
theorem minusSquareBound_nonneg {M : ℕ} {y : ℝ} (hy : 0 < y) (hM : y < (M : ℝ) + 1) :
    0 ≤ minusSquareBound M y := by
  apply (tsum_nonneg (fun n : ℕ => show 0 ≤ 1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - y) ^ 2) by positivity)).trans
  exact harmonic_tail_square_bound hy hM

/-- The upper cube coefficient is nonnegative because it bounds the actual positive series. -/
theorem minusCubeBound_nonneg {M : ℕ} {y : ℝ} (hy : 0 < y) (hM : y < (M : ℝ) + 1) :
    0 ≤ minusCubeBound M y := by
  apply (tsum_nonneg (fun n : ℕ => show 0 ≤ 1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - y) ^ 3) by
    have hn : 0 < (n : ℝ) + M + 1 - y := by linarith [Nat.cast_nonneg (α := ℝ) n]
    positivity)).trans
  exact harmonic_tail_cube_bound hy hM

/-- Combining the two amplitude majorants yields exactly the source H/H₁ terms. -/
theorem negativeModeError_pair_le {f g : ℝ → ℝ} {a b : ℝ}
    (hfa : 0 < deriv f a) {M : ℕ} (hM : deriv f a < (M : ℝ) + 1) (hfd : DifferentiableAt ℝ (deriv f) a)
    (hgd : DifferentiableAt ℝ g a) :
    negativeModeError (deriv f) (deriv (deriv f)) (deriv g) (deriv (deriv g)) a b M +
      2 * Real.pi * negativeModeError (deriv f) (deriv (deriv f))
        (fun u => g u * deriv f u) (deriv (fun u => g u * deriv f u)) a b M ≤
      secondH f g b / (4 * Real.pi ^ 2) * ‖negativeTail M b (deriv f b)‖ +
      secondH f g a / (4 * Real.pi ^ 2) * ‖negativeTail M a (deriv f a)‖ +
      secondH1 f g a / (4 * Real.pi ^ 3) * minusSquareBound M (deriv f a) +
      (secondH f g a * |deriv (deriv f) a| / (4 * Real.pi ^ 3)) * minusCubeBound M (deriv f a) := by
  have hd : deriv (fun u => g u * deriv f u) a =
      deriv g a * deriv f a + g a * deriv (deriv f) a :=
    (hgd.hasDerivAt.mul hfd.hasDerivAt).deriv
  have hb := abs_add_le (deriv g a * deriv f a) (g a * deriv (deriv f) a)
  have hc : 0 ≤ 2 * Real.pi / (4 * Real.pi ^ 3) * minusSquareBound M (deriv f a) :=
    mul_nonneg (by positivity) (minusSquareBound_nonneg hfa hM)
  have ht := mul_le_mul_of_nonneg_right hb hc
  unfold negativeModeError secondH secondH1
  rw [hd]
  simp only [abs_mul] at ht ⊢
  simp only [div_eq_mul_inv] at ht ⊢
  nlinarith only [ht]

/-- The exact upper coefficient identity transfers proved bounds on the two actual amplitude series. -/
theorem norm_negativeCoefficient_le_mode_errors {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) (M : ℕ) (hM : deriv f a < (M : ℝ) + 1)
    (hg : Summable (upperModeTerm f (deriv g) a b M))
    (hgf : Summable (upperModeTerm f (fun u => g u * deriv f u) a b M))
    (bg : ‖∑' n : ℕ, upperModeTerm f (deriv g) a b M n‖ ≤
      negativeModeError (deriv f) (deriv (deriv f)) (deriv g) (deriv (deriv g)) a b M)
    (bgf : ‖∑' n : ℕ, upperModeTerm f (fun u => g u * deriv f u) a b M n‖ ≤
      negativeModeError (deriv f) (deriv (deriv f))
        (fun u => g u * deriv f u) (deriv (fun u => g u * deriv f u)) a b M)
    (hfd : DifferentiableAt ℝ (deriv f) a) :
    ‖∑' n : ℕ, negativeCoefficient f g a b (n + M + 1)‖ ≤
      secondH f g b / (4 * Real.pi ^ 2) * ‖negativeTail M b (deriv f b)‖ +
      secondH f g a / (4 * Real.pi ^ 2) * ‖negativeTail M a (deriv f a)‖ +
      secondH1 f g a / (4 * Real.pi ^ 3) * minusSquareBound M (deriv f a) +
      (secondH f g a * |deriv (deriv f) a| / (4 * Real.pi ^ 3)) * minusCubeBound M (deriv f a) := by
  rw [tsum_negativeCoefficient_eq_upperModes h M hg hgf]
  apply (norm_add_le _ _).trans
  rw [norm_div, Complex.norm_I, div_one, norm_mul]
  have hc : ‖2 * (Real.pi : ℂ)‖ = 2 * Real.pi := by simp
  rw [hc]
  exact (add_le_add bg (mul_le_mul_of_nonneg_left bgf (by positivity))).trans
    (negativeModeError_pair_le (h.f_deriv_pos a (Set.left_mem_Icc.mpr h.lt.le)) hM hfd
      (h.g_differentiable a (Set.left_mem_Icc.mpr h.lt.le)))


/-- The actual AFE upper Poisson tail satisfies the complete H/H₁ bound, with all integral estimates derived. -/
theorem afe_negativeCoefficient_bound {σ c a b : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) (M : ℕ) (hM : c / a < (M : ℝ) + 1) :
    ‖∑' n : ℕ, negativeCoefficient (afePhase c) (afeWeight σ) a b (n + M + 1)‖ ≤
      secondH (afePhase c) (afeWeight σ) b / (4 * Real.pi ^ 2) * ‖negativeTail M b (c / b)‖ +
      secondH (afePhase c) (afeWeight σ) a / (4 * Real.pi ^ 2) * ‖negativeTail M a (c / a)‖ +
      secondH1 (afePhase c) (afeWeight σ) a / (4 * Real.pi ^ 3) * minusSquareBound M (c / a) +
      (secondH (afePhase c) (afeWeight σ) a * (c / a ^ 2) / (4 * Real.pi ^ 3)) * minusCubeBound M (c / a) := by
  have hr := afe_partIRegularity hσ hc ha hab
  have hg := afe_upper_second_tail_bound hσ hc ha hab (deriv (afeWeight σ)) (Or.inl rfl) hM
  have hgf := afe_upper_second_tail_bound hσ hc ha hab
    (fun u => afeWeight σ u * deriv (afePhase c) u) (Or.inr rfl) hM
  have hn := norm_negativeCoefficient_le_mode_errors hr M
    (by simpa only [(afePhase_hasDerivAt c ha).deriv] using hM) hg.1 hgf.1
    (show ‖∑' n : ℕ, upperModeTerm (afePhase c) (deriv (afeWeight σ)) a b M n‖ ≤
      negativeModeError (deriv (afePhase c)) (deriv (deriv (afePhase c)))
        (deriv (afeWeight σ)) (deriv (deriv (afeWeight σ))) a b M by
      simpa only [negativeModeError, minusSquareBound, minusCubeBound,
        (afePhase_hasDerivAt c ha).deriv, (afePhase_hasDerivAt c (ha.trans hab)).deriv,
        (afePhase_deriv_hasDerivAt c ha).deriv] using hg.2)
    (show ‖∑' n : ℕ, upperModeTerm (afePhase c) (fun u => afeWeight σ u * deriv (afePhase c) u) a b M n‖ ≤
      negativeModeError (deriv (afePhase c)) (deriv (deriv (afePhase c)))
        (fun u => afeWeight σ u * deriv (afePhase c) u)
        (deriv (fun u => afeWeight σ u * deriv (afePhase c) u)) a b M by
      simpa only [negativeModeError, minusSquareBound, minusCubeBound,
        (afePhase_hasDerivAt c ha).deriv, (afePhase_hasDerivAt c (ha.trans hab)).deriv,
        (afePhase_deriv_hasDerivAt c ha).deriv] using hgf.2)
    (afePhase_deriv_hasDerivAt c ha).differentiableAt
  simpa only [(afePhase_hasDerivAt c ha).deriv, (afePhase_hasDerivAt c (ha.trans hab)).deriv,
    (afePhase_deriv_hasDerivAt c ha).deriv, abs_div, abs_neg, abs_of_pos hc,
    abs_of_nonneg (sq_nonneg a)] using hn


/-- The actual finite AFE Poisson remainder satisfies the assembled second-order bound before the separate E₁/E₂ packaging. -/
theorem afe_finite_poisson_second_bound {σ c a b : ℝ} (hσ : 0 ≤ σ) (hc : 0 < c)
    (ha : 0 < a) (hab : a < b) :
    let f : ℝ → ℝ := afePhase c
    let g : ℝ → ℝ := afeWeight σ
    let M : ℕ := ⌊c / a⌋₊
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) - poissonMain f g a b M‖ ≤
      ‖poissonHeadBoundary f g b M‖ + ‖poissonHeadBoundary f g a M‖ + ‖poissonBoundary f g a b‖ +
      secondH f g b / (4 * Real.pi ^ 2) *
        (‖negativeTail M b (c / b)‖ + ‖positiveTail (-b) (c / b)‖) +
      secondH f g a / (4 * Real.pi ^ 2) *
        (‖negativeTail M a (c / a)‖ + ‖positiveTail (-a) (c / a)‖) +
      secondH1 f g a / (4 * Real.pi ^ 3) *
        (minusSquareBound M (c / a) + plusSquareBound (c / a)) +
      (secondH f g a * (c / a ^ 2) / (4 * Real.pi ^ 3)) *
        (minusCubeBound M (c / a) + plusCubeBound (c / a)) := by
  dsimp only
  have hr := afe_partIRegularity hσ hc ha hab
  have hp := afe_positiveCoefficient_bound hσ hc ha hab
  have hn := afe_negativeCoefficient_bound hσ hc ha hab ⌊c / a⌋₊ (Nat.lt_floor_add_one (c / a))
  have hs (A B N P G : ℂ) : ‖A - B + N - P + G‖ ≤ ‖A‖ + ‖B‖ + ‖N‖ + ‖P‖ + ‖G‖ := by
    have h1 := norm_sub_le A B
    have h2 := norm_add_le (A - B) N
    have h3 := norm_sub_le (A - B + N) P
    have h4 := norm_add_le (A - B + N - P) G
    linarith
  rw [weighted_sum_eq_poissonMain_add_remainder hr]
  apply (hs _ _ _ _ _).trans
  simp only [div_eq_mul_inv] at hp hn ⊢
  nlinarith only [hp, hn]

/-- The actual sum of source square coefficients equals the proved E₁ envelope divided by y. -/
theorem squareBounds_eq_proposed_envelope {y : ℝ} (hy : 0 < y) :
    minusSquareBound ⌊y⌋₊ y + plusSquareBound y = partIISquareTailEnvelope y / y := by
  unfold minusSquareBound plusSquareBound partIISquareTailEnvelope
  dsimp only
  rw [show (⌊y⌋₊ : ℝ) + 1 - y = 1 - (y - (⌊y⌋₊ : ℝ)) by ring]
  have hy1 : y + 1 ≠ 0 := by positivity
  have h1y : 1 + y ≠ 0 := by positivity
  field_simp
  ring

/-- The unchanged literal E₂ coefficient from auxillary_error2 in the frozen source. -/
noncomputable def partIICubeCoefficient (y : ℝ) : ℝ :=
  let δ : ℝ := 1 - (y - (⌊y⌋₊ : ℝ))
  1 / δ ^ 3 + 1 / (δ + 1) ^ 3 + 1 / (2 * (δ + 1) ^ 2) -
    1 / y * (1 / δ ^ 2 + 1 / (δ + 1)) +
    1 / y ^ 2 * (Real.log ((⌊y⌋₊ : ℝ) + 1) - 1 / (2 * ((⌊y⌋₊ : ℝ) + 1)) -
      (Complex.digamma (δ : ℂ)).re + Real.log (y + 1) + Real.eulerMascheroniConstant -
      (3 * y + 3 * y ^ 2 + 1) / (2 * (1 + y) ^ 2))

/-- The two cube coefficients assemble to the unchanged source E₂ expression. -/
theorem cubeBounds_eq_source_coefficient {y : ℝ} (hy : 0 < y) :
    minusCubeBound ⌊y⌋₊ y + plusCubeBound y = partIICubeCoefficient y / y := by
  unfold minusCubeBound plusCubeBound partIICubeCoefficient
  dsimp only
  rw [show (⌊y⌋₊ : ℝ) + 1 - y = 1 - (y - (⌊y⌋₊ : ℝ)) by ring]
  have hy1 : y + 1 ≠ 0 := by positivity
  have h1y : 1 + y ≠ 0 := by positivity
  field_simp
  ring

/-- The unchanged E₂ coefficient bounds the two actual cube-denominator tails. -/
theorem partII_cube_coefficient_bound {y : ℝ} (hy : 0 < y) :
    (∑' n : ℕ, 1 / (((n : ℝ) + ⌊y⌋₊ + 1) * ((n : ℝ) + ⌊y⌋₊ + 1 - y) ^ 3)) +
      (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + y) ^ 3)) ≤ partIICubeCoefficient y / y := by
  rw [← cubeBounds_eq_source_coefficient hy]
  exact add_le_add (harmonic_tail_cube_bound hy (Nat.lt_floor_add_one y)) (harmonic_plus_cube_bound hy)

end DhimanKadiriQuesadaHerrera2026
