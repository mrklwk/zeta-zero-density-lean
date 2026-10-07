module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.SecondModeTails

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Actual second-integration series above the stationary cutoff -/

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory
open scoped Topology

/-- The actual upper-frequency integral with its original Fourier denominator. -/
noncomputable def upperModeTerm (f h : ℝ → ℝ) (a b : ℝ) (M n : ℕ) : ℂ :=
  (∫ u in a..b, (h u : ℂ) * exp (2 * (Real.pi : ℂ) * I *
    ((f u - ((n : ℝ) + M + 1) * u : ℝ) : ℂ))) / (2 * (Real.pi : ℂ) * ((n : ℂ) + M + 1))

/-- The upper-frequency endpoint contribution, retaining the signed derivative denominator. -/
noncomputable def upperModeEndpoint (f p h : ℝ → ℝ) (x : ℝ) (M n : ℕ) : ℂ :=
  ((h x / (p x - ((n : ℝ) + M + 1)) : ℝ) : ℂ) *
    exp (2 * (Real.pi : ℂ) * I * ((f x - ((n : ℝ) + M + 1) * x : ℝ) : ℂ)) /
      (2 * (Real.pi : ℂ) * I) / (2 * (Real.pi : ℂ) * ((n : ℂ) + M + 1))

/-- The signed upper endpoint factors into its endpoint amplitude and the actual negative-shift harmonic mode. -/
theorem upperModeEndpoint_eq (f p h : ℝ → ℝ) (x : ℝ) (M n : ℕ) :
    upperModeEndpoint f p h x M n =
      (-((h x : ℂ) * exp (2 * (Real.pi : ℂ) * I * (f x : ℂ)) / (4 * (Real.pi : ℂ) ^ 2 * I))) *
        (expMode x (n + M + 1) / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - p x) : ℝ)) := by
  unfold upperModeEndpoint expMode
  have he : 2 * (Real.pi : ℂ) * I * ((f x - ((n : ℝ) + M + 1) * x : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * I * (f x : ℂ) +
        (-2 * (Real.pi : ℂ) * I * ((n + M + 1 : ℕ) : ℂ) * (x : ℂ)) := by
    push_cast
    ring
  rw [he, exp_add]
  have hd : p x - ((n : ℝ) + M + 1) = -(((n : ℝ) + M + 1) - p x) := by ring
  rw [hd]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev, inv_neg]
  ring_nf

/-- Absolute convergence of the actual upper-frequency endpoint series. -/
theorem summable_upperModeEndpoint (f p h : ℝ → ℝ) {x : ℝ} {M : ℕ}
    (hp : 0 < p x) (hM : p x < (M : ℝ) + 1) :
    Summable (upperModeEndpoint f p h x M) := by
  change Summable (fun n => upperModeEndpoint f p h x M n)
  simp_rw [upperModeEndpoint_eq]
  exact (summable_negative_tail_shift hp hM x).mul_left _

/-- The upper endpoint series is exactly the existing negative-shift oscillatory tail. -/
theorem tsum_upperModeEndpoint (f p h : ℝ → ℝ) {x : ℝ} {M : ℕ}
    (hp : 0 < p x) (hM : p x < (M : ℝ) + 1) :
    (∑' n : ℕ, upperModeEndpoint f p h x M n) =
      (-((h x : ℂ) * exp (2 * (Real.pi : ℂ) * I * (f x : ℂ)) / (4 * (Real.pi : ℂ) ^ 2 * I))) *
        negativeTail M x (p x) := by
  simp_rw [upperModeEndpoint_eq]
  rw [tsum_mul_left, negativeTail_eq_shift hp hM]
  congr 1
  apply tsum_congr
  intro n
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Norm of the exact upper endpoint series preserves oscillatory cancellation. -/
theorem norm_tsum_upperModeEndpoint (f p h : ℝ → ℝ) {x : ℝ} {M : ℕ}
    (hp : 0 < p x) (hM : p x < (M : ℝ) + 1) :
    ‖∑' n : ℕ, upperModeEndpoint f p h x M n‖ =
      |h x| / (4 * Real.pi ^ 2) * ‖negativeTail M x (p x)‖ := by
  rw [tsum_upperModeEndpoint f p h hp hM, norm_mul, norm_neg, norm_div, norm_mul]
  have he : ‖exp (2 * (Real.pi : ℂ) * I * (f x : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [he]
  simp [Real.norm_eq_abs]

/-- Each upper-frequency remainder has the exact square/cube bound after Fourier normalization. -/
theorem upperModeTerm_remainder_bound {a b : ℝ} (hab : a < b)
    {f p p' h h' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (p' u) u)
    (hh : ∀ u ∈ Set.Icc a b, HasDerivAt h (h' u) u)
    (hpc : ContinuousOn p (Set.Icc a b)) (hppc : ContinuousOn p' (Set.Icc a b))
    (hhpc : ContinuousOn h' (Set.Icc a b))
    (hpa : AntitoneOn p (Set.Icc a b))
    (hha : AntitoneOn (fun u => |h u|) (Set.Icc a b))
    (hhpa : AntitoneOn (fun u => |h' u|) (Set.Icc a b))
    (hppa : AntitoneOn (fun u => |p' u|) (Set.Icc a b))
    {M : ℕ} (hM : p a < (M : ℝ) + 1) (n : ℕ) :
    ‖upperModeTerm f h a b M n - (upperModeEndpoint f p h b M n - upperModeEndpoint f p h a M n)‖ ≤
      (|h' a| / (4 * Real.pi ^ 3)) * (1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - p a) ^ 2)) +
        (|h a * p' a| / (4 * Real.pi ^ 3)) * (1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - p a) ^ 3)) := by
  have hn : p a < (n : ℝ) + M + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hb := norm_negative_exp_integral_sub_boundary_le hab hf hp hh hpc hppc hhpc hpa hha hhpa hppa hn
  have hn0 : 0 < 2 * Real.pi * ((n : ℝ) + M + 1) := by positivity
  have hb' := div_le_div_of_nonneg_right hb hn0.le
  have he : upperModeTerm f h a b M n - (upperModeEndpoint f p h b M n - upperModeEndpoint f p h a M n) =
      ((∫ u in a..b, (h u : ℂ) * exp (2 * (Real.pi : ℂ) * I *
        ((f u - ((n : ℝ) + M + 1) * u : ℝ) : ℂ))) -
        (((h b / (p b - ((n : ℝ) + M + 1)) : ℝ) : ℂ) * exp (2 * (Real.pi : ℂ) * I *
          ((f b - ((n : ℝ) + M + 1) * b : ℝ) : ℂ)) -
        ((h a / (p a - ((n : ℝ) + M + 1)) : ℝ) : ℂ) * exp (2 * (Real.pi : ℂ) * I *
          ((f a - ((n : ℝ) + M + 1) * a : ℝ) : ℂ))) / (2 * (Real.pi : ℂ) * I)) /
        (2 * (Real.pi : ℂ) * ((n : ℂ) + M + 1)) := by
    unfold upperModeTerm upperModeEndpoint
    simp only [div_eq_mul_inv]
    ring
  rw [he, norm_div]
  have hd : ‖2 * (Real.pi : ℂ) * ((n : ℂ) + M + 1)‖ = 2 * Real.pi * ((n : ℝ) + M + 1) := by
    have he : 2 * (Real.pi : ℂ) * ((n : ℂ) + M + 1) =
        ((2 * Real.pi * ((n : ℝ) + M + 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn0]
  rw [hd]
  convert hb' using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The complete upper-frequency integral series converges and satisfies the actual negative-tail bound. -/
theorem upperModeTail_bound {a b : ℝ} (hab : a < b)
    {f p p' h h' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (p' u) u)
    (hh : ∀ u ∈ Set.Icc a b, HasDerivAt h (h' u) u)
    (hpc : ContinuousOn p (Set.Icc a b)) (hppc : ContinuousOn p' (Set.Icc a b))
    (hhpc : ContinuousOn h' (Set.Icc a b))
    (hpa : AntitoneOn p (Set.Icc a b))
    (hha : AntitoneOn (fun u => |h u|) (Set.Icc a b))
    (hhpa : AntitoneOn (fun u => |h' u|) (Set.Icc a b))
    (hppa : AntitoneOn (fun u => |p' u|) (Set.Icc a b))
    (hpos : ∀ u ∈ Set.Icc a b, 0 < p u) {M : ℕ} (hM : p a < (M : ℝ) + 1) :
    Summable (upperModeTerm f h a b M) ∧
    ‖∑' n : ℕ, upperModeTerm f h a b M n‖ ≤
      |h b| / (4 * Real.pi ^ 2) * ‖negativeTail M b (p b)‖ +
      |h a| / (4 * Real.pi ^ 2) * ‖negativeTail M a (p a)‖ +
      (|h' a| / (4 * Real.pi ^ 3)) * (∑' n : ℕ, 1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - p a) ^ 2)) +
      (|h a * p' a| / (4 * Real.pi ^ 3)) * (∑' n : ℕ, 1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - p a) ^ 3)) := by
  have ha := hpos a (Set.left_mem_Icc.mpr hab.le)
  have hb := hpos b (Set.right_mem_Icc.mpr hab.le)
  have hMb : p b < (M : ℝ) + 1 :=
    (hpa (Set.left_mem_Icc.mpr hab.le) (Set.right_mem_Icc.mpr hab.le) hab.le).trans_lt hM
  let R : ℕ → ℂ := fun n => upperModeTerm f h a b M n -
    (upperModeEndpoint f p h b M n - upperModeEndpoint f p h a M n)
  let A : ℝ := |h' a| / (4 * Real.pi ^ 3)
  let B : ℝ := |h a * p' a| / (4 * Real.pi ^ 3)
  let w2 : ℕ → ℝ := fun n => 1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - p a) ^ 2)
  let w3 : ℕ → ℝ := fun n => 1 / (((n : ℝ) + M + 1) * ((n : ℝ) + M + 1 - p a) ^ 3)
  have hs2 : Summable w2 := (hasSum_harmonic_tail_square ha hM).summable
  have hs3 : Summable w3 := (hasSum_harmonic_tail_cube ha hM).summable
  have hs := (hs2.mul_left A).add (hs3.mul_left B)
  have hbound (n : ℕ) : ‖R n‖ ≤ A * w2 n + B * w3 n :=
    upperModeTerm_remainder_bound hab hf hp hh hpc hppc hhpc hpa hha hhpa hppa hM n
  have hsR : Summable R := hs.of_norm_bounded hbound
  have hsEa := summable_upperModeEndpoint f p h ha hM
  have hsEb := summable_upperModeEndpoint f p h hb hMb
  have hseq : upperModeTerm f h a b M = fun n =>
      R n + (upperModeEndpoint f p h b M n - upperModeEndpoint f p h a M n) := by
    funext n
    exact (sub_add_cancel _ _).symm
  refine ⟨?_, ?_⟩
  · rw [hseq]
    exact hsR.add (hsEb.sub hsEa)
  · have hr : ‖∑' n, R n‖ ≤ A * ∑' n, w2 n + B * ∑' n, w3 n := by
      have ht := tsum_of_norm_bounded hs.hasSum hbound
      simpa only [Summable.tsum_add (hs2.mul_left A) (hs3.mul_left B), tsum_mul_left] using ht
    rw [hseq, hsR.tsum_add (hsEb.sub hsEa), hsEb.tsum_sub hsEa]
    have hn := (norm_add_le (∑' n, R n)
      ((∑' n, upperModeEndpoint f p h b M n) - ∑' n, upperModeEndpoint f p h a M n)).trans
        (add_le_add hr (norm_sub_le _ _))
    rw [norm_tsum_upperModeEndpoint f p h hb hMb, norm_tsum_upperModeEndpoint f p h ha hM] at hn
    dsimp only [A, B, w2, w3] at hn
    linarith

/-- The complete source square/cube coefficients bound the upper-frequency integral series. -/
theorem upperModeTail_source_bound {a b : ℝ} (hab : a < b)
    {f p p' h h' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (p' u) u)
    (hh : ∀ u ∈ Set.Icc a b, HasDerivAt h (h' u) u)
    (hpc : ContinuousOn p (Set.Icc a b)) (hppc : ContinuousOn p' (Set.Icc a b))
    (hhpc : ContinuousOn h' (Set.Icc a b))
    (hpa : AntitoneOn p (Set.Icc a b))
    (hha : AntitoneOn (fun u => |h u|) (Set.Icc a b))
    (hhpa : AntitoneOn (fun u => |h' u|) (Set.Icc a b))
    (hppa : AntitoneOn (fun u => |p' u|) (Set.Icc a b))
    (hpos : ∀ u ∈ Set.Icc a b, 0 < p u) {M : ℕ} (hM : p a < (M : ℝ) + 1) :
    let δ : ℝ := (M : ℝ) + 1 - p a
    ‖∑' n : ℕ, upperModeTerm f h a b M n‖ ≤
      |h b| / (4 * Real.pi ^ 2) * ‖negativeTail M b (p b)‖ +
      |h a| / (4 * Real.pi ^ 2) * ‖negativeTail M a (p a)‖ +
      (|h' a| / (4 * Real.pi ^ 3)) *
        ((1 / δ ^ 2 + 1 / (δ + 1) ^ 2 + 1 / (δ + 1)) / p a -
          (Real.log ((M : ℝ) + 1) - 1 / ((M : ℝ) + 1) -
            (Complex.digamma (δ : ℂ)).re) / (p a) ^ 2) +
      (|h a * p' a| / (4 * Real.pi ^ 3)) *
        ((1 / δ ^ 3 + 1 / (δ + 1) ^ 3 + 1 / (2 * (δ + 1) ^ 2)) / p a -
          (1 / δ ^ 2 + 1 / (δ + 1)) / (p a) ^ 2 +
          (Real.log ((M : ℝ) + 1) - 1 / (2 * ((M : ℝ) + 1)) -
            (Complex.digamma (δ : ℂ)).re) / (p a) ^ 3) := by
  have ha := hpos a (Set.left_mem_Icc.mpr hab.le)
  apply (upperModeTail_bound hab hf hp hh hpc hppc hhpc hpa hha hhpa hppa hpos hM).2.trans
  exact add_le_add
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (harmonic_tail_square_bound ha hM) (by positivity)))
    (mul_le_mul_of_nonneg_left (harmonic_tail_cube_bound ha hM) (by positivity))

end DhimanKadiriQuesadaHerrera2026
