module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.OscillatoryParts
public import WeylPort.AFE.ExponentialTails

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Actual positive-frequency second-integration series

These technical estimates expose their analytic quotient conditions explicitly.
The corrected general Part-II consumer is in CorrectedPartII.
-/

namespace DhimanKadiriQuesadaHerrera2026
open Complex MeasureTheory
open scoped Topology

/-- The actual positive-frequency integral divided by its Fourier coefficient. -/
noncomputable def secondModeTerm (f h : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℂ :=
  (∫ u in a..b, (h u : ℂ) * exp (2 * (Real.pi : ℂ) * I *
    ((f u + ((n : ℝ) + 1) * u : ℝ) : ℂ))) / (2 * (Real.pi : ℂ) * ((n : ℂ) + 1))

/-- The endpoint contribution from the second integration by parts, with its complex factor. -/
noncomputable def secondModeEndpoint (f p h : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℂ :=
  ((h x / (((n : ℝ) + 1) + p x) : ℝ) : ℂ) *
    exp (2 * (Real.pi : ℂ) * I * ((f x + ((n : ℝ) + 1) * x : ℝ) : ℂ)) /
      (2 * (Real.pi : ℂ) * I) / (2 * (Real.pi : ℂ) * ((n : ℂ) + 1))

/-- The boundary coefficient is the actual positive-shift harmonic mode times its endpoint amplitude. -/
theorem secondModeEndpoint_eq (f p h : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    secondModeEndpoint f p h x n =
      ((h x : ℂ) * exp (2 * (Real.pi : ℂ) * I * (f x : ℂ)) / (4 * (Real.pi : ℂ) ^ 2 * I)) *
        (expMode (-x) (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 1 + p x) : ℝ)) := by
  unfold secondModeEndpoint expMode
  have he : 2 * (Real.pi : ℂ) * I * ((f x + ((n : ℝ) + 1) * x : ℝ) : ℂ) =
      2 * (Real.pi : ℂ) * I * (f x : ℂ) +
        (-2 * (Real.pi : ℂ) * I * ((n + 1 : ℕ) : ℂ) * ((-x : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [he, exp_add]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring_nf

/-- The actual endpoint series is absolutely convergent. -/
theorem summable_secondModeEndpoint (f p h : ℝ → ℝ) {x : ℝ} (hp : 0 < p x) :
    Summable (secondModeEndpoint f p h x) := by
  change Summable (fun n => secondModeEndpoint f p h x n)
  simp_rw [secondModeEndpoint_eq]
  exact (summable_positive_tail_shift hp (-x)).mul_left _

/-- The endpoint series sums to the existing oscillatory positive tail. -/
theorem tsum_secondModeEndpoint (f p h : ℝ → ℝ) {x : ℝ} (hp : 0 < p x) :
    (∑' n : ℕ, secondModeEndpoint f p h x n) =
      ((h x : ℂ) * exp (2 * (Real.pi : ℂ) * I * (f x : ℂ)) / (4 * (Real.pi : ℂ) ^ 2 * I)) *
        positiveTail (-x) (p x) := by
  simp_rw [secondModeEndpoint_eq]
  rw [tsum_mul_left, positiveTail_eq_shift hp]
  congr 1
  apply tsum_congr
  intro n
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- Norm of the exact endpoint series retains its oscillatory cancellation. -/
theorem norm_tsum_secondModeEndpoint (f p h : ℝ → ℝ) {x : ℝ} (hp : 0 < p x) :
    ‖∑' n : ℕ, secondModeEndpoint f p h x n‖ =
      |h x| / (4 * Real.pi ^ 2) * ‖positiveTail (-x) (p x)‖ := by
  rw [tsum_secondModeEndpoint f p h hp, norm_mul, norm_div, norm_mul]
  have he : ‖exp (2 * (Real.pi : ℂ) * I * (f x : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [he]
  simp [Real.norm_eq_abs]

/-- An actual mode minus its exact endpoints satisfies the square/cube Fourier remainder bound. -/
theorem secondModeTerm_remainder_bound {a b : ℝ} (hab : a < b)
    {f p p' h h' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (p' u) u)
    (hh : ∀ u ∈ Set.Icc a b, HasDerivAt h (h' u) u)
    (hpc : ContinuousOn p (Set.Icc a b)) (hppc : ContinuousOn p' (Set.Icc a b))
    (hhpc : ContinuousOn h' (Set.Icc a b))
    (hpos : ∀ u ∈ Set.Icc a b, 0 < p u) (n : ℕ)
    (hq1 : AntitoneOn (fun u => |h' u| / (((n : ℝ) + 1) + p u) ^ 2) (Set.Icc a b))
    (hq2 : AntitoneOn (fun u => |h u * p' u| / (((n : ℝ) + 1) + p u) ^ 3) (Set.Icc a b)) :
    ‖secondModeTerm f h a b n - (secondModeEndpoint f p h b n - secondModeEndpoint f p h a n)‖ ≤
      (|h' a| / (4 * Real.pi ^ 3)) * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + p a) ^ 2)) +
        (|h a * p' a| / (4 * Real.pi ^ 3)) * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + p a) ^ 3)) := by
  have hn (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < ((n : ℝ) + 1) + p u := by
    have := hpos u hu
    positivity
  have hb := norm_expMode_integral_sub_boundary_le hab
    (fun u hu => by
      simpa only [mul_one, add_comm, id_eq] using (hf u hu).fun_add ((hasDerivAt_id u).const_mul ((n : ℝ) + 1)))
    (fun u hu => (hp u hu).const_add ((n : ℝ) + 1)) hh
    (continuousOn_const.add hpc) hppc hhpc (fun u hu => (hn u hu).ne') hq1
    (by
      intro u hu v hv huv
      dsimp only
      rw [abs_of_pos (hn u hu), abs_of_pos (hn v hv)]
      exact hq2 hu hv huv)
  have hea := Set.left_mem_Icc.mpr hab.le
  rw [abs_of_pos (hn a hea)] at hb
  have hn0 : 0 < 2 * Real.pi * ((n : ℝ) + 1) := by positivity
  have hb' := div_le_div_of_nonneg_right hb hn0.le
  have he : secondModeTerm f h a b n - (secondModeEndpoint f p h b n - secondModeEndpoint f p h a n) =
      ((∫ u in a..b, (h u : ℂ) * exp (2 * (Real.pi : ℂ) * I *
        ((f u + ((n : ℝ) + 1) * u : ℝ) : ℂ))) -
        (((h b / (((n : ℝ) + 1) + p b) : ℝ) : ℂ) * exp (2 * (Real.pi : ℂ) * I *
          ((f b + ((n : ℝ) + 1) * b : ℝ) : ℂ)) -
        ((h a / (((n : ℝ) + 1) + p a) : ℝ) : ℂ) * exp (2 * (Real.pi : ℂ) * I *
          ((f a + ((n : ℝ) + 1) * a : ℝ) : ℂ))) / (2 * (Real.pi : ℂ) * I)) /
        (2 * (Real.pi : ℂ) * ((n : ℂ) + 1)) := by
    unfold secondModeTerm secondModeEndpoint
    simp only [div_eq_mul_inv]
    ring
  rw [he, norm_div]
  have hd : ‖2 * (Real.pi : ℂ) * ((n : ℂ) + 1)‖ = 2 * Real.pi * ((n : ℝ) + 1) := by
    have he : 2 * (Real.pi : ℂ) * ((n : ℂ) + 1) =
        ((2 * Real.pi * ((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn0]
  rw [hd]
  convert hb' using 1
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual positive-frequency integral series converges, and its bound retains both endpoint cancellations and both harmonic tails. -/
theorem secondModeTail_bound {a b : ℝ} (hab : a < b)
    {f p p' h h' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (p' u) u)
    (hh : ∀ u ∈ Set.Icc a b, HasDerivAt h (h' u) u)
    (hpc : ContinuousOn p (Set.Icc a b)) (hppc : ContinuousOn p' (Set.Icc a b))
    (hhpc : ContinuousOn h' (Set.Icc a b))
    (hpos : ∀ u ∈ Set.Icc a b, 0 < p u)
    (hq1 : ∀ n : ℕ, AntitoneOn (fun u => |h' u| / (((n : ℝ) + 1) + p u) ^ 2) (Set.Icc a b))
    (hq2 : ∀ n : ℕ, AntitoneOn (fun u => |h u * p' u| / (((n : ℝ) + 1) + p u) ^ 3) (Set.Icc a b)) :
    Summable (secondModeTerm f h a b) ∧
    ‖∑' n : ℕ, secondModeTerm f h a b n‖ ≤
      |h b| / (4 * Real.pi ^ 2) * ‖positiveTail (-b) (p b)‖ +
      |h a| / (4 * Real.pi ^ 2) * ‖positiveTail (-a) (p a)‖ +
      (|h' a| / (4 * Real.pi ^ 3)) * (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + p a) ^ 2)) +
      (|h a * p' a| / (4 * Real.pi ^ 3)) * (∑' n : ℕ, 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + p a) ^ 3)) := by
  have ha := hpos a (Set.left_mem_Icc.mpr hab.le)
  have hb := hpos b (Set.right_mem_Icc.mpr hab.le)
  let R : ℕ → ℂ := fun n => secondModeTerm f h a b n -
    (secondModeEndpoint f p h b n - secondModeEndpoint f p h a n)
  let A : ℝ := |h' a| / (4 * Real.pi ^ 3)
  let B : ℝ := |h a * p' a| / (4 * Real.pi ^ 3)
  let w2 : ℕ → ℝ := fun n => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + p a) ^ 2)
  let w3 : ℕ → ℝ := fun n => 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 + p a) ^ 3)
  have hs2 : Summable w2 := (hasSum_harmonic_plus_square ha).summable
  have hs3 : Summable w3 := (hasSum_harmonic_plus_cube ha).summable
  have hs := (hs2.mul_left A).add (hs3.mul_left B)
  have hbound (n : ℕ) : ‖R n‖ ≤ A * w2 n + B * w3 n :=
    secondModeTerm_remainder_bound hab hf hp hh hpc hppc hhpc hpos n (hq1 n) (hq2 n)
  have hsR : Summable R := hs.of_norm_bounded hbound
  have hsEa := summable_secondModeEndpoint f p h ha
  have hsEb := summable_secondModeEndpoint f p h hb
  have hseq : secondModeTerm f h a b = fun n =>
      R n + (secondModeEndpoint f p h b n - secondModeEndpoint f p h a n) := by
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
      ((∑' n, secondModeEndpoint f p h b n) - ∑' n, secondModeEndpoint f p h a n)).trans
        (add_le_add hr (norm_sub_le _ _))
    rw [norm_tsum_secondModeEndpoint f p h hb, norm_tsum_secondModeEndpoint f p h ha] at hn
    dsimp only [A, B, w2, w3] at hn
    linarith

/-- Lemma 1 gives the full source logarithmic square/cube coefficients for the actual positive-frequency integral sum. -/
theorem secondModeTail_source_bound {a b : ℝ} (hab : a < b)
    {f p p' h h' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (p' u) u)
    (hh : ∀ u ∈ Set.Icc a b, HasDerivAt h (h' u) u)
    (hpc : ContinuousOn p (Set.Icc a b)) (hppc : ContinuousOn p' (Set.Icc a b))
    (hhpc : ContinuousOn h' (Set.Icc a b))
    (hpos : ∀ u ∈ Set.Icc a b, 0 < p u)
    (hq1 : ∀ n : ℕ, AntitoneOn (fun u => |h' u| / (((n : ℝ) + 1) + p u) ^ 2) (Set.Icc a b))
    (hq2 : ∀ n : ℕ, AntitoneOn (fun u => |h u * p' u| / (((n : ℝ) + 1) + p u) ^ 3) (Set.Icc a b)) :
    ‖∑' n : ℕ, secondModeTerm f h a b n‖ ≤
      |h b| / (4 * Real.pi ^ 2) * ‖positiveTail (-b) (p b)‖ +
      |h a| / (4 * Real.pi ^ 2) * ‖positiveTail (-a) (p a)‖ +
      (|h' a| / (4 * Real.pi ^ 3)) *
        ((Real.log (p a + 1) + Real.eulerMascheroniConstant) / (p a) ^ 2 -
          (1 + 2 * p a) / (2 * (p a) ^ 2 * (p a + 1))) +
      (|h a * p' a| / (4 * Real.pi ^ 3)) *
        ((Real.log (p a + 1) + Real.eulerMascheroniConstant) / (p a) ^ 3 -
          (1 + 3 * p a + 3 * (p a) ^ 2) / (2 * (p a) ^ 3 * (p a + 1) ^ 2)) := by
  have ha := hpos a (Set.left_mem_Icc.mpr hab.le)
  apply (secondModeTail_bound hab hf hp hh hpc hppc hhpc hpos hq1 hq2).2.trans
  exact add_le_add
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (harmonic_plus_square_bound ha) (by positivity)))
    (mul_le_mul_of_nonneg_left (harmonic_plus_cube_bound ha) (by positivity))

end DhimanKadiriQuesadaHerrera2026
