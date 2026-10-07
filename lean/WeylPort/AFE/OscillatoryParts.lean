module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.FirstDerivativeTest

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Exact integration by parts and the second oscillatory remainder

The analytic quotient hypotheses are explicit. This technical lemma does not
adopt a repaired general Part-II contract or assume a final remainder bound.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex MeasureTheory

/-- Integration by parts retains the actual complex boundary factor 1/i. -/
theorem oscillatory_integral_parts {a b : ℝ} {f p p' h h' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.uIcc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.uIcc a b, HasDerivAt p (p' u) u)
    (hh : ∀ u ∈ Set.uIcc a b, HasDerivAt h (h' u) u)
    (hpc : ContinuousOn p (Set.uIcc a b)) (hppc : ContinuousOn p' (Set.uIcc a b))
    (hhpc : ContinuousOn h' (Set.uIcc a b)) (hn : ∀ u ∈ Set.uIcc a b, p u ≠ 0) :
    (∫ u in a..b, (h u : ℂ) * exp (I * (f u : ℂ))) =
      ((h b / p b : ℝ) * exp (I * (f b : ℂ)) -
        (h a / p a : ℝ) * exp (I * (f a : ℂ))) / I -
      (∫ u in a..b, (((h' u * p u - h u * p' u) / (p u) ^ 2 : ℝ) : ℂ) *
        exp (I * (f u : ℂ))) / I := by
  have hhc : ContinuousOn h (Set.uIcc a b) := fun u hu => (hh u hu).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Set.uIcc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have he (u : ℝ) (hu : u ∈ Set.uIcc a b) :
      HasDerivAt (fun v => exp (I * (f v : ℂ)))
        ((I * (p u : ℂ)) * exp (I * (f u : ℂ))) u := by
    convert (((hf u hu).ofReal_comp.const_mul I).cexp) using 1
    ring
  have hq (u : ℝ) (hu : u ∈ Set.uIcc a b) :
      HasDerivAt (fun v => ((h v / p v : ℝ) : ℂ))
        (((h' u * p u - h u * p' u) / (p u) ^ 2 : ℝ) : ℂ) u :=
    ((hh u hu).div (hp u hu) (hn u hu)).ofReal_comp
  have hqc : ContinuousOn (fun u => (((h' u * p u - h u * p' u) / (p u) ^ 2 : ℝ) : ℂ))
      (Set.uIcc a b) := Complex.continuous_ofReal.comp_continuousOn
    (((hhpc.mul hpc).sub (hhc.mul hppc)).div (hpc.pow 2) (fun u hu => pow_ne_zero _ (hn u hu)))
  have hec : ContinuousOn (fun u => (I * (p u : ℂ)) * exp (I * (f u : ℂ)))
      (Set.uIcc a b) := by fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hq he
    hqc.intervalIntegrable hec.intervalIntegrable
  have hi : (∫ u in a..b, ((h u / p u : ℝ) : ℂ) *
      ((I * (p u : ℂ)) * exp (I * (f u : ℂ)))) =
      I * (∫ u in a..b, (h u : ℂ) * exp (I * (f u : ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    have hn' : (p u : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hn u hu)
    push_cast
    field_simp
  rw [hi] at hparts
  rw [← sub_div]
  apply (eq_div_iff I_ne_zero).mpr
  linear_combination hparts

/-- The explicit second-integration remainder follows from two actual quotient monotonicity conditions.
The assumptions are analytic conditions on the amplitudes, not a supplied remainder estimate. -/
theorem norm_oscillatory_integral_sub_boundary_le {a b : ℝ} (hab : a < b)
    {f p p' h h' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (p' u) u)
    (hh : ∀ u ∈ Set.Icc a b, HasDerivAt h (h' u) u)
    (hpc : ContinuousOn p (Set.Icc a b)) (hppc : ContinuousOn p' (Set.Icc a b))
    (hhpc : ContinuousOn h' (Set.Icc a b)) (hn : ∀ u ∈ Set.Icc a b, p u ≠ 0)
    (hq1 : AntitoneOn (fun u => |h' u| / (p u) ^ 2) (Set.Icc a b))
    (hq2 : AntitoneOn (fun u => |h u * p' u| / |p u| ^ 3) (Set.Icc a b)) :
    ‖(∫ u in a..b, (h u : ℂ) * exp (I * (f u : ℂ))) -
      ((h b / p b : ℝ) * exp (I * (f b : ℂ)) -
        (h a / p a : ℝ) * exp (I * (f a : ℂ))) / I‖ ≤
      2 * |h' a| / (p a) ^ 2 + 2 * |h a * p' a| / |p a| ^ 3 := by
  have hhc : ContinuousOn h (Set.Icc a b) := fun u hu => (hh u hu).continuousAt.continuousWithinAt
  have hfc : ContinuousOn f (Set.Icc a b) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have ha1 : ContinuousOn (fun u => h' u / p u) (Set.Icc a b) := hhpc.div hpc hn
  have ha2 : ContinuousOn (fun u => h u * p' u / (p u) ^ 2) (Set.Icc a b) :=
    (hhc.mul hppc).div (hpc.pow 2) (fun u hu => pow_ne_zero _ (hn u hu))
  have he1 (u : ℝ) : |(h' u / p u) / p u| = |h' u| / (p u) ^ 2 := by
    rw [div_div, ← pow_two, abs_div, abs_of_nonneg (sq_nonneg (p u))]
  have he2 (u : ℝ) : |(h u * p' u / (p u) ^ 2) / p u| = |h u * p' u| / |p u| ^ 3 := by
    rw [div_div, ← pow_succ, abs_div, abs_pow]
  have hb1 := first_derivative_test_antitone hab hf hpc ha1 hn
    (by simpa only [he1] using hq1)
  have hb2 := first_derivative_test_antitone hab hf hpc ha2 hn
    (by simpa only [he2] using hq2)
  rw [he1] at hb1
  rw [he2] at hb2
  have hc1 : ContinuousOn (fun u => ((h' u / p u : ℝ) : ℂ) * exp (I * (f u : ℂ)))
      (Set.Icc a b) := by fun_prop
  have hc2 : ContinuousOn (fun u => ((h u * p' u / (p u) ^ 2 : ℝ) : ℂ) * exp (I * (f u : ℂ)))
      (Set.Icc a b) := by fun_prop
  have he : (∫ u in a..b, (((h' u * p u - h u * p' u) / (p u) ^ 2 : ℝ) : ℂ) *
      exp (I * (f u : ℂ))) =
      (∫ u in a..b, ((h' u / p u : ℝ) : ℂ) * exp (I * (f u : ℂ))) -
      (∫ u in a..b, ((h u * p' u / (p u) ^ 2 : ℝ) : ℂ) * exp (I * (f u : ℂ))) := by
    rw [← intervalIntegral.integral_sub (Set.uIcc_of_le hab.le ▸ hc1).intervalIntegrable
      (Set.uIcc_of_le hab.le ▸ hc2).intervalIntegrable]
    apply intervalIntegral.integral_congr
    intro u hu
    have hn' : (p u : ℂ) ≠ 0 := ofReal_ne_zero.mpr (hn u (Set.uIcc_of_le hab.le ▸ hu))
    push_cast
    field_simp
  rw [oscillatory_integral_parts (Set.uIcc_of_le hab.le ▸ hf) (Set.uIcc_of_le hab.le ▸ hp)
    (Set.uIcc_of_le hab.le ▸ hh) (Set.uIcc_of_le hab.le ▸ hpc)
    (Set.uIcc_of_le hab.le ▸ hppc) (Set.uIcc_of_le hab.le ▸ hhpc)
    (Set.uIcc_of_le hab.le ▸ hn), sub_sub_cancel_left, norm_neg, norm_div, norm_I, div_one, he]
  apply (norm_sub_le _ _).trans
  simpa only [mul_div_assoc] using add_le_add hb1 hb2

/-- Source 2π normalization of the second-integration estimate, with its exact complex endpoint term. -/
theorem norm_expMode_integral_sub_boundary_le {a b : ℝ} (hab : a < b)
    {f p p' h h' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (p' u) u)
    (hh : ∀ u ∈ Set.Icc a b, HasDerivAt h (h' u) u)
    (hpc : ContinuousOn p (Set.Icc a b)) (hppc : ContinuousOn p' (Set.Icc a b))
    (hhpc : ContinuousOn h' (Set.Icc a b)) (hn : ∀ u ∈ Set.Icc a b, p u ≠ 0)
    (hq1 : AntitoneOn (fun u => |h' u| / (p u) ^ 2) (Set.Icc a b))
    (hq2 : AntitoneOn (fun u => |h u * p' u| / |p u| ^ 3) (Set.Icc a b)) :
    ‖(∫ u in a..b, (h u : ℂ) * exp (2 * (Real.pi : ℂ) * I * (f u : ℂ))) -
      ((h b / p b : ℝ) * exp (2 * (Real.pi : ℂ) * I * (f b : ℂ)) -
        (h a / p a : ℝ) * exp (2 * (Real.pi : ℂ) * I * (f a : ℂ))) /
          (2 * (Real.pi : ℂ) * I)‖ ≤
      |h' a| / (2 * Real.pi ^ 2 * (p a) ^ 2) +
        |h a * p' a| / (2 * Real.pi ^ 2 * |p a| ^ 3) := by
  have he1 (u : ℝ) : |h' u| / (2 * Real.pi * p u) ^ 2 =
      (1 / (2 * Real.pi) ^ 2) * (|h' u| / (p u) ^ 2) := by ring
  have he2 (u : ℝ) : |h u * (2 * Real.pi * p' u)| / |2 * Real.pi * p u| ^ 3 =
      (1 / (2 * Real.pi) ^ 2) * (|h u * p' u| / |p u| ^ 3) := by
    rw [show h u * (2 * Real.pi * p' u) = (2 * Real.pi) * (h u * p' u) by ring,
      abs_mul (2 * Real.pi) (h u * p' u), abs_of_pos Real.two_pi_pos,
      abs_mul (2 * Real.pi) (p u), abs_of_pos Real.two_pi_pos]
    field_simp
  have hbound := norm_oscillatory_integral_sub_boundary_le hab
    (fun u hu => (hf u hu).const_mul (2 * Real.pi))
    (fun u hu => (hp u hu).const_mul (2 * Real.pi)) hh
    (continuousOn_const.mul hpc) (continuousOn_const.mul hppc) hhpc
    (fun u hu => mul_ne_zero Real.two_pi_pos.ne' (hn u hu))
    (by
      intro u hu v hv huv
      dsimp only
      rw [he1 u, he1 v]
      exact mul_le_mul_of_nonneg_left (hq1 hu hv huv) (by positivity))
    (by
      intro u hu v hv huv
      dsimp only
      rw [he2 u, he2 v]
      exact mul_le_mul_of_nonneg_left (hq2 hu hv huv) (by positivity))
  have hexp (u : ℝ) : exp (I * ((2 * Real.pi * f u : ℝ) : ℂ)) =
      exp (2 * (Real.pi : ℂ) * I * (f u : ℂ)) := by
    congr 1
    push_cast
    ring
  simp only [hexp] at hbound
  have hb : (((h b / (2 * Real.pi * p b) : ℝ) : ℂ) *
      exp (2 * (Real.pi : ℂ) * I * (f b : ℂ)) -
      ((h a / (2 * Real.pi * p a) : ℝ) : ℂ) *
      exp (2 * (Real.pi : ℂ) * I * (f a : ℂ))) / I =
      (((h b / p b : ℝ) : ℂ) * exp (2 * (Real.pi : ℂ) * I * (f b : ℂ)) -
      ((h a / p a : ℝ) : ℂ) * exp (2 * (Real.pi : ℂ) * I * (f a : ℂ))) /
        (2 * (Real.pi : ℂ) * I) := by
    push_cast
    ring
  rw [hb] at hbound
  apply hbound.trans_eq
  rw [show 2 * |h' a| / (2 * Real.pi * p a) ^ 2 =
    2 * (|h' a| / (2 * Real.pi * p a) ^ 2) by ring, he1,
    show 2 * |h a * (2 * Real.pi * p' a)| / |2 * Real.pi * p a| ^ 3 =
    2 * (|h a * (2 * Real.pi * p' a)| / |2 * Real.pi * p a| ^ 3) by ring, he2]
  ring

/-- Above the phase-derivative cutoff, the source's decreasing absolute amplitudes imply both quotient conditions. -/
theorem negative_second_quotients_antitone {a b ν : ℝ} {p p' h h' : ℝ → ℝ}
    (hab : a ≤ b) (hpa : AntitoneOn p (Set.Icc a b))
    (hha : AntitoneOn (fun u => |h u|) (Set.Icc a b))
    (hhpa : AntitoneOn (fun u => |h' u|) (Set.Icc a b))
    (hppa : AntitoneOn (fun u => |p' u|) (Set.Icc a b)) (hν : p a < ν) :
    AntitoneOn (fun u => |h' u| / (p u - ν) ^ 2) (Set.Icc a b) ∧
    AntitoneOn (fun u => |h u * p' u| / |p u - ν| ^ 3) (Set.Icc a b) := by
  have hgap (u : ℝ) (hu : u ∈ Set.Icc a b) : 0 < ν - p u := by
    have hp := hpa (Set.left_mem_Icc.mpr hab) hu hu.1
    linarith
  refine ⟨?_, ?_⟩
  · intro u hu v hv huv
    dsimp only
    rw [show (p v - ν) ^ 2 = (ν - p v) ^ 2 by ring,
      show (p u - ν) ^ 2 = (ν - p u) ^ 2 by ring]
    apply div_le_div₀ (abs_nonneg _) (hhpa hu hv huv) (sq_pos_of_pos (hgap u hu))
    exact pow_le_pow_left₀ (hgap u hu).le (by linarith [hpa hu hv huv]) 2
  · intro u hu v hv huv
    dsimp only
    rw [abs_of_neg (by linarith [hgap v hv] : p v - ν < 0), neg_sub,
      abs_of_neg (by linarith [hgap u hu] : p u - ν < 0), neg_sub]
    apply div_le_div₀ (abs_nonneg _) _ (pow_pos (hgap u hu) 3)
      (pow_le_pow_left₀ (hgap u hu).le (by linarith [hpa hu hv huv]) 3)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (hha hu hv huv) (hppa hu hv huv) (abs_nonneg _) (abs_nonneg _)

/-- The source's negative-frequency second-integration estimate follows without additional quotient hypotheses. -/
theorem norm_negative_exp_integral_sub_boundary_le {a b ν : ℝ} (hab : a < b)
    {f p p' h h' : ℝ → ℝ}
    (hf : ∀ u ∈ Set.Icc a b, HasDerivAt f (p u) u)
    (hp : ∀ u ∈ Set.Icc a b, HasDerivAt p (p' u) u)
    (hh : ∀ u ∈ Set.Icc a b, HasDerivAt h (h' u) u)
    (hpc : ContinuousOn p (Set.Icc a b)) (hppc : ContinuousOn p' (Set.Icc a b))
    (hhpc : ContinuousOn h' (Set.Icc a b)) (hpa : AntitoneOn p (Set.Icc a b))
    (hha : AntitoneOn (fun u => |h u|) (Set.Icc a b))
    (hhpa : AntitoneOn (fun u => |h' u|) (Set.Icc a b))
    (hppa : AntitoneOn (fun u => |p' u|) (Set.Icc a b)) (hν : p a < ν) :
    ‖(∫ u in a..b, (h u : ℂ) * exp (2 * (Real.pi : ℂ) * I * ((f u - ν * u : ℝ) : ℂ))) -
      (((h b / (p b - ν) : ℝ) : ℂ) * exp (2 * (Real.pi : ℂ) * I * ((f b - ν * b : ℝ) : ℂ)) -
        ((h a / (p a - ν) : ℝ) : ℂ) * exp (2 * (Real.pi : ℂ) * I * ((f a - ν * a : ℝ) : ℂ))) /
          (2 * (Real.pi : ℂ) * I)‖ ≤
      |h' a| / (2 * Real.pi ^ 2 * (ν - p a) ^ 2) +
        |h a * p' a| / (2 * Real.pi ^ 2 * (ν - p a) ^ 3) := by
  have hq := negative_second_quotients_antitone hab.le hpa hha hhpa hppa hν
  have hd (u : ℝ) (hu : u ∈ Set.Icc a b) :
      HasDerivAt (fun v => f v - ν * v) (p u - ν) u := by
    simpa only [mul_one, id_eq] using (hf u hu).fun_sub ((hasDerivAt_id u).const_mul ν)
  have hn (u : ℝ) (hu : u ∈ Set.Icc a b) : p u - ν ≠ 0 := by
    have h := hpa (Set.left_mem_Icc.mpr hab.le) hu hu.1
    apply ne_of_lt
    linarith
  have hbound := norm_expMode_integral_sub_boundary_le hab hd
    (fun u hu => (hp u hu).sub_const ν) hh (hpc.sub continuousOn_const) hppc hhpc hn hq.1 hq.2
  simpa only [show (p a - ν) ^ 2 = (ν - p a) ^ 2 by ring,
    abs_of_neg (sub_neg.mpr hν), neg_sub] using hbound

end DhimanKadiriQuesadaHerrera2026
