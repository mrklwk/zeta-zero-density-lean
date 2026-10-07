module
/- Extracted from PNT (Apache-2.0), via pinned McColm source; see analytic-extraction.json. -/
public import Mathlib

@[expose] public section

-- Lean 4.34 elaborator compatibility; kernel checking stays enabled.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ZetaAppendix
open Real Complex MeasureTheory Finset Filter Topology Set Summable
private noncomputable def e (α : ℝ) : ℂ := exp (2 * π * I * α)
/-- For C¹ functions `g` and `F`, the error in integration by parts is bounded by
`sup ‖F‖ · ∫ |g'|`. -/
private theorem lemma_IBP_bound_C1 {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hg : ContDiffOn ℝ 1 g (Icc a b)) (hF : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
        (⨆ t ∈ Icc a b, ‖F t‖) * ∫ t in Icc a b, |deriv g t| := by
  have hint_parts : ∫ t in Icc a b, (g t) * (deriv F t) =
      (g b) * (F b) - (g a) * (F a) - ∫ t in Icc a b, (F t) * (deriv g t) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
        eq_sub_iff_add_eq, ← intervalIntegral.integral_add, intervalIntegral.integral_eq_sub_of_hasDeriv_right]
    · rw [Set.uIcc_of_le hab.le]
      exact ContinuousOn.mul
        (continuous_ofReal.comp_continuousOn hg.continuousOn) hF.continuousOn
    · intro x hx
      have hxa : x > a := by cases max_cases a b <;> cases min_cases a b <;> linarith [hx.1, hx.2]
      have hxb : x < b := by cases max_cases a b <;> cases min_cases a b <;> linarith [hx.1, hx.2]
      convert HasDerivAt.hasDerivWithinAt <| HasDerivAt.mul
        (HasDerivAt.ofReal_comp <| hg.differentiableOn_one |> DifferentiableOn.hasDerivAt <| Icc_mem_nhds hxa hxb)
          (hF.differentiableOn_one |> DifferentiableOn.hasDerivAt <| Icc_mem_nhds hxa hxb)
            using 1
      ring
    · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
      refine Integrable.add ?_ ?_
      · have hintF : IntegrableOn (fun x ↦ deriv F x) (Ioo a b) := by
          have hcont := hF.continuousOn_derivWithin
          have hintF' : IntegrableOn (fun x ↦ derivWithin F (Icc a b) x) (Ioo a b) :=
            (hcont (uniqueDiffOn_Icc hab) le_rfl |> ContinuousOn.integrableOn_Icc) |>
              fun h ↦ h.mono_set Ioo_subset_Icc_self
          refine hintF'.congr ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using
            by exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
        apply Integrable.mono' _ _ _
        · exact fun x ↦ ‖deriv F x‖ * sSup (Set.image (fun x ↦ |g x|) (Icc a b))
        · exact Integrable.mul_const hintF.norm _
        · exact AEStronglyMeasurable.mul
            (continuous_ofReal.comp_aestronglyMeasurable
              (hg.continuousOn.aestronglyMeasurable measurableSet_Icc |>
                fun h ↦ h.mono_set Ioo_subset_Icc_self))
            hintF.aestronglyMeasurable
        · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using by
            simpa [mul_comm] using mul_le_mul_of_nonneg_left
              (le_csSup (IsCompact.bddAbove (isCompact_Icc.image_of_continuousOn
                (continuous_abs.comp_continuousOn hg.continuousOn)))
                (Set.mem_image_of_mem _ <| Ioo_subset_Icc_self hx)) (norm_nonneg _)
      · have hintg : IntegrableOn (fun x ↦ deriv g x) (Ioo a b) := by
          have hcont := hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
          have hintg' : IntegrableOn (fun x ↦ derivWithin g (Icc a b) x) (Ioo a b) :=
            hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
          exact hintg'.congr_fun (fun x hx ↦
            by exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)) measurableSet_Ioo
        have hintFg : IntegrableOn (fun x ↦ F x * deriv g x) (Ioo a b) := by
          have hbdd : ∃ C, ∀ x ∈ Ioo a b, ‖F x‖ ≤ C :=
            IsCompact.exists_bound_of_continuousOn isCompact_Icc hF.continuousOn |>
              fun ⟨C, hC⟩ ↦ ⟨C, fun x hx ↦ hC x <| Ioo_subset_Icc_self hx⟩
          apply Integrable.mono' _ _ _
          · exact fun x ↦ hbdd.choose * ‖deriv g x‖
          · exact Integrable.const_mul hintg.norm _
          · exact AEStronglyMeasurable.mul
              (hF.continuousOn.aestronglyMeasurable measurableSet_Icc |>
                fun h ↦ h.mono_set Ioo_subset_Icc_self)
              (continuous_ofReal.comp_aestronglyMeasurable hintg.aestronglyMeasurable)
          · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using by
              simpa using mul_le_mul_of_nonneg_right (hbdd.choose_spec x hx)
                (norm_nonneg (deriv g x))
        exact hintFg
    · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
      have hintF : IntegrableOn (fun x ↦ deriv F x) (Ioo a b) := by
        have hcont := hF.continuousOn_derivWithin
        have hintF' : IntegrableOn (fun x ↦ derivWithin F (Icc a b) x) (Ioo a b) :=
          (hcont (uniqueDiffOn_Icc hab) le_rfl |> ContinuousOn.integrableOn_Icc) |>
            fun h ↦ h.mono_set Ioo_subset_Icc_self
        refine hintF'.congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using
          by exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
      refine hintF.norm.const_mul ?_ |> fun h ↦ h.mono' ?_ ?_
      · exact sSup (Set.image (fun x ↦ ‖g x‖) (Icc a b))
      · exact AEStronglyMeasurable.mul
          (continuous_ofReal.comp_aestronglyMeasurable
            (hg.continuousOn.aestronglyMeasurable measurableSet_Icc |>
              fun h ↦ h.mono_set Ioo_subset_Icc_self))
          hintF.aestronglyMeasurable
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx using by
          simpa [abs_mul] using mul_le_mul_of_nonneg_right
            (le_csSup (IsCompact.bddAbove (isCompact_Icc.image_of_continuousOn hg.continuousOn.norm))
              (Set.mem_image_of_mem _ <| Ioo_subset_Icc_self hx)) (norm_nonneg _)
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
      have hintg : IntegrableOn (fun x ↦ deriv g x) (Ioc a b) := by
        have hintg' : IntegrableOn (fun x ↦ deriv g x) (Ioo a b) := by
          have hcont := hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
          have hintg'' : IntegrableOn (fun x ↦ derivWithin g (Icc a b) x) (Ioo a b) :=
            hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
          exact hintg''.congr_fun (fun x hx ↦
            by exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)) measurableSet_Ioo
        rw [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Ioc] at *
        assumption
      have hintFg : IntegrableOn (fun x ↦ F x * deriv g x) (Ioc a b) := by
        have hbdd : ∃ C, ∀ x ∈ Ioc a b, ‖F x‖ ≤ C :=
          IsCompact.exists_bound_of_continuousOn isCompact_Icc hF.continuousOn |>
            fun ⟨C, hC⟩ ↦ ⟨C, fun x hx ↦ hC x <| Ioc_subset_Icc_self hx⟩
        apply Integrable.mono' _ _ _
        · exact fun x ↦ hbdd.choose * ‖deriv g x‖
        · exact Integrable.const_mul hintg.norm _
        · exact AEStronglyMeasurable.mul
            (hF.continuousOn.aestronglyMeasurable measurableSet_Icc |>
              fun h ↦ h.mono_set Ioc_subset_Icc_self)
            (continuous_ofReal.comp_aestronglyMeasurable hintg.aestronglyMeasurable)
        · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx using by
            simpa using mul_le_mul_of_nonneg_right (hbdd.choose_spec x hx)
              (norm_nonneg (deriv g x))
      convert hintFg using 1
  simp_all only [sub_sub_cancel_left, norm_neg, Set.mem_Icc, ge_iff_le]
  rw [← integral_const_mul]
  refine le_trans (norm_integral_le_integral_norm _) (integral_mono_of_nonneg ?_ ?_ ?_)
  · exact Eventually.of_forall fun x ↦ norm_nonneg _
  · refine Integrable.const_mul ?_ _
    have hderivint : IntegrableOn (deriv g) (Ioo a b) := by
      have hcont := hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
      exact (hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self) |> fun h ↦ h.congr_fun
        (fun x hx ↦ by exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)) measurableSet_Ioo
    simpa only [IntegrableOn, Measure.restrict_congr_set Ioo_ae_eq_Icc] using hderivint.abs
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_ciSup ?_ t) (abs_nonneg _))
    · aesop
    · obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hF.continuousOn.norm
      exact ⟨Max.max M 1, Set.forall_mem_range.mpr fun t ↦ by rw [ciSup_eq_ite]; aesop⟩

/-- Integration by parts bound for `C¹` monotone functions.
For `C¹` monotone `g` and `C¹` `F`, `‖∫ g F' - [gF]‖ ≤ sup ‖F‖ · (g(b) - g(a))`. -/
private theorem lemma_IBP_bound_C1_monotone {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hg : ContDiffOn ℝ 1 g (Icc a b)) (hg_mono : MonotoneOn g (Icc a b))
    (hF : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
    (⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a) := by
  have hbound := @lemma_IBP_bound_C1 a b hab g F hg hF
  have hdiff : DifferentiableOn ℝ g (Icc a b) := hg.differentiableOn_one
  have hderiv_nonneg : ∀ t ∈ Ioo a b, 0 ≤ deriv g t := by
    intro t ht
    have hlim : Tendsto (fun h ↦ (g (t + h) - g t) / h) (𝓝[Ioi 0] 0) (𝓝 (deriv g t)) := by
      have hHasDeriv : HasDerivAt g (deriv g t) t :=
        hdiff.differentiableAt (Icc_mem_nhds ht.1 ht.2) |>.hasDerivAt
      simpa [div_eq_inv_mul] using hHasDeriv.tendsto_slope_zero_right
    refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
    filter_upwards [Ioo_mem_nhdsGT (sub_pos.mpr ht.2)] with h hh
    apply div_nonneg
    · rw [sub_nonneg]
      refine hg_mono (Ioo_subset_Icc_self ht) ?_ (by linarith [hh.1])
      rw [Set.mem_Icc]
      constructor <;> linarith [ht.1, ht.2, hh.1, hh.2]
    · exact hh.1.le
  have hint_deriv : ∫ t in Icc a b, deriv g t = g b - g a := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hg.continuousOn
    · intro t ht
      exact hdiff.differentiableAt (Icc_mem_nhds ht.1 ht.2) |>.hasDerivAt
    · rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le]
      have hcont_dw := hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
      refine hcont_dw.integrableOn_Icc.mono_set Ioo_subset_Icc_self |>.congr_fun ?_ measurableSet_Ioo
      intro x hx
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  have hint_abs : ∫ t in Icc a b, |deriv g t| = ∫ t in Icc a b, deriv g t := by
    simp only [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx ↦ ?_
    rw [abs_of_nonneg (hderiv_nonneg x hx)]
  rw [hint_abs, hint_deriv] at hbound
  exact hbound

open scoped unitInterval in
/-- The Bernstein approximation of a monotone function is monotone. -/
private theorem bernsteinApproximation_monotone (n : ℕ) (f : C(I, ℝ)) (hf : Monotone f) :
    Monotone (bernsteinApproximation n f) := by
  intro x y hxy
  simp only [bernsteinApproximation, smul_eq_mul, ContinuousMap.coe_sum, ContinuousMap.coe_mul,
    ContinuousMap.coe_const, Finset.sum_apply, Pi.mul_apply, Function.const_apply]
  have hmono : ∀ i j : Fin (n + 1), i ≤ j → f (bernstein.z i) ≤ f (bernstein.z j) :=
    fun i j hij ↦ hf <| Subtype.mk_le_mk.mpr <| by simpa [bernstein.z] using by gcongr; aesop
  have hsum : ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      (bernstein n i x * bernstein n j y - bernstein n i y * bernstein n j x) *
        (f (bernstein.z j) - f (bernstein.z i)) ≥ 0 := by
    refine Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ ?_
    by_cases hij : i ≤ j
    · refine mul_nonneg ?_ (sub_nonneg.mpr (hmono i j hij))
      have hineq : x.val ^ (i : ℕ) * (1 - x.val) ^ (n - i : ℕ) * y.val ^ (j : ℕ) *
          (1 - y.val) ^ (n - j : ℕ) ≥ x.val ^ (j : ℕ) * (1 - x.val) ^ (n - j : ℕ) *
          y.val ^ (i : ℕ) * (1 - y.val) ^ (n - i : ℕ) := by
        have hdiv : y.val ^ (j - i : ℕ) * (1 - x.val) ^ (j - i : ℕ) ≥
            x.val ^ (j - i : ℕ) * (1 - y.val) ^ (j - i : ℕ) := by
          rw [← mul_pow, ← mul_pow]
          exact pow_le_pow_left₀ (mul_nonneg (Subtype.property x |>.1)
            (sub_nonneg.2 (Subtype.property y |>.2)))
            (by nlinarith [show (x : ℝ) ≤ y from hxy, show (x : ℝ) ≥ 0 from Subtype.property x |>.1,
              show (y : ℝ) ≤ 1 from Subtype.property y |>.2]) _
        simp_all only [Finset.mem_univ, ge_iff_le, mul_comm, mul_left_comm, mul_assoc]
        convert mul_le_mul_of_nonneg_left hdiv (show 0 ≤ (x : ℝ) ^ (i : ℕ) * (y : ℝ) ^ (i : ℕ) *
            (1 - x : ℝ) ^ (n - j : ℕ) * (1 - y : ℝ) ^ (n - j : ℕ) by
          exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (mod_cast x.2.1) _)
            (pow_nonneg (mod_cast y.2.1) _)) (pow_nonneg (sub_nonneg.2 <| mod_cast x.2.2) _))
            (pow_nonneg (sub_nonneg.2 <| mod_cast y.2.2) _)) using 1 <;> ring_nf
        · simp only [mul_assoc, ← pow_add, add_tsub_cancel_of_le (show (i : ℕ) ≤ j from hij),
            mul_eq_mul_left_iff, pow_eq_zero_iff', ne_eq, Icc.coe_eq_zero, Fin.val_eq_zero_iff]
          exact Or.inl <| Or.inl <| Or.inl <|
            by rw [tsub_add_tsub_cancel (mod_cast Fin.is_le _) (mod_cast hij)]
        · simp only [mul_assoc, ← pow_add, add_tsub_cancel_of_le (show (i : ℕ) ≤ j from hij),
            mul_eq_mul_left_iff, mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq, Icc.coe_eq_zero,
            Fin.val_eq_zero_iff]
          exact Or.inl <| Or.inl <| Or.inl <|
            by rw [tsub_add_tsub_cancel (mod_cast Fin.is_le _) (mod_cast hij)]
      simp_all only [Finset.mem_univ, ge_iff_le, bernstein, Polynomial.toContinuousMapOn_apply,
        Polynomial.toContinuousMap_apply, sub_nonneg]
      simp_all only [bernsteinPolynomial, Polynomial.eval_mul, Polynomial.eval_natCast,
        Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_one]
      convert mul_le_mul_of_nonneg_left hineq
        (show 0 ≤ (n.choose i : ℝ) * (n.choose j : ℝ) by positivity) using 1 <;> ring
    · refine mul_nonneg_of_nonpos_of_nonpos ?_ ?_
      · norm_num [bernstein, bernsteinPolynomial]
        have hexp : (x.val : ℝ) ^ (i : ℕ) * (y.val : ℝ) ^ (j : ℕ) ≤
            (x.val : ℝ) ^ (j : ℕ) * (y.val : ℝ) ^ (i : ℕ) := by
          rw [show (i : ℕ) = j + (i - j) by rw [Nat.add_sub_cancel' (le_of_not_ge hij)]]
          ring_nf
          rw [mul_right_comm]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by exact_mod_cast x.2.1)
            (by exact_mod_cast hxy) _) (mul_nonneg (pow_nonneg (by exact_mod_cast x.2.1) _)
            (pow_nonneg (by exact_mod_cast y.2.1) _))
        have hexp2 : (1 - x.val) ^ (n - i.val) * (1 - y.val) ^ (n - j.val) ≤
            (1 - x.val) ^ (n - j.val) * (1 - y.val) ^ (n - i.val) := by
          rw [show n - (i : ℕ) = n - (j : ℕ) - (i - j : ℕ) by
            rw [tsub_tsub, add_tsub_cancel_of_le (mod_cast le_of_not_ge hij)]]
          rw [show (1 - x.val) ^ (n - j.val) = (1 - x.val) ^ (n - j.val - (i.val - j.val)) *
              (1 - x.val) ^ (i.val - j.val) by rw [← pow_add, Nat.sub_add_cancel
              (show (i.val - j.val) ≤ n - j.val from Nat.sub_le_sub_right (mod_cast Fin.is_le i) _)],
            show (1 - y.val) ^ (n - j.val) = (1 - y.val) ^ (n - j.val - (i.val - j.val)) *
              (1 - y.val) ^ (i.val - j.val) by rw [← pow_add, Nat.sub_add_cancel
              (show (i.val - j.val) ≤ n - j.val from Nat.sub_le_sub_right (mod_cast Fin.is_le i) _)]]
          rw [mul_assoc, mul_comm ((1 - x.val) ^ (i.val - j.val))]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (sub_nonneg.2 <| mod_cast y.2.2)
            (sub_le_sub_left (mod_cast hxy) _) _) <| pow_nonneg (sub_nonneg.2 <| mod_cast y.2.2) _)
            <| pow_nonneg (sub_nonneg.2 <| mod_cast x.2.2) _
        convert mul_le_mul_of_nonneg_left (mul_le_mul hexp hexp2 (?_) (?_))
          (show (0 : ℝ) ≤ (n.choose i : ℝ) * (n.choose j : ℝ) by positivity) using 1 <;> ring_nf
        · exact mul_nonneg (pow_nonneg (sub_nonneg.2 <| mod_cast x.2.2) _)
            (pow_nonneg (sub_nonneg.2 <| mod_cast y.2.2) _)
        · exact mul_nonneg (pow_nonneg (Subtype.property x |>.1) _)
            (pow_nonneg (Subtype.property y |>.1) _)
      · exact sub_nonpos_of_le <| hmono _ _ <| le_of_not_ge hij
  contrapose! hsum
  simp_all only [mul_comm, mul_sub, sum_sub_distrib, ← Finset.mul_sum _ _ _, bernstein.probability,
    one_mul, sub_neg]
  simp_all only [← mul_assoc, ← sum_comm, ← sum_mul, ← Finset.mul_sum _ _ _, bernstein.probability,
    mul_one]
  linarith

open scoped unitInterval in
/-- Continuous monotone functions on `[0,1]` can be uniformly approximated by smooth monotone
functions (polynomials). -/
private theorem lemma_approx_monotone_C1_I (f : C(I, ℝ)) (hf_mono : Monotone f) :
    ∀ ε > 0, ∃ P : ℝ → ℝ, ContDiffOn ℝ 1 P I ∧ MonotoneOn P I ∧ ∀ x : I, |f x - P x| < ε := by
  intro ε hεpos
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.mp (tendsto_iff_norm_sub_tendsto_zero.mp
    (bernsteinApproximation_uniform f)) ε hεpos
  have hn : ‖bernsteinApproximation n f - f‖ < ε := by simpa [dist_zero_right, norm_norm] using hn n le_rfl
  let P : ℝ → ℝ := fun x ↦ ∑ k : Fin (n + 1), (n.choose k : ℝ) * x ^ (k : ℕ) * (1 - x) ^ (n - k : ℕ) * f (bernstein.z k)
  have hP (x) (hx : x ∈ I) : P x = bernsteinApproximation n f ⟨x, hx⟩ := by
    simp [P, bernsteinApproximation, bernstein, bernsteinPolynomial, mul_comm]
  refine ⟨P, ContDiff.contDiffOn <| ContDiff.sum fun k _ ↦ ?_, fun x hx y hy hxy ↦ ?_, fun x ↦ ?_⟩
  · apply_rules [ContDiff.mul, ContDiff.pow, contDiff_const, contDiff_id, ContDiff.sub]
  · rw [hP x hx, hP y hy]
    exact bernsteinApproximation_monotone n f hf_mono (Subtype.mk_le_mk.mpr hxy)
  · rw [abs_sub_comm, hP x x.2]
    exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm (bernsteinApproximation n f - f) x) hn

/-- Continuous monotone functions on a compact interval can be uniformly approximated by `C¹`
monotone functions. -/
private theorem lemma_approx_monotone_C1 {a b : ℝ} (hab : a < b) (g : ℝ → ℝ)
    (hg_cont : ContinuousOn g (Set.Icc a b)) (hg_mono : MonotoneOn g (Set.Icc a b)) :
    ∀ ε > 0, ∃ g' : ℝ → ℝ, ContDiffOn ℝ 1 g' (Set.Icc a b) ∧ MonotoneOn g' (Set.Icc a b) ∧
      ∀ x ∈ Set.Icc a b, |g x - g' x| < ε := by
  intro ε hε_pos
  set f := fun t : unitInterval ↦ g (a + t.val * (b - a)) with hf_def
  obtain ⟨P, hP_cont, hP_mono, hP_approx⟩ : ∃ P : ℝ → ℝ, ContDiffOn ℝ 1 P unitInterval ∧
    MonotoneOn P unitInterval ∧ ∀ t : unitInterval, |f t - P t| < ε := by
    have hf_cont : ContinuousOn f (Set.univ : Set unitInterval) :=
      hg_cont.comp (Continuous.continuousOn (by continuity)) fun x hx ↦
        ⟨by nlinarith [x.2.1, x.2.2], by nlinarith [x.2.1, x.2.2]⟩
    have hf_mono : Monotone f :=
      fun x y hxy ↦ hg_mono ⟨by nlinarith [x.2.1, x.2.2], by nlinarith [x.2.1, x.2.2]⟩ ⟨by nlinarith [y.2.1, y.2.2],
        by nlinarith [y.2.1, y.2.2]⟩ (by nlinarith [x.2.1, x.2.2, y.2.1, y.2.2, show (x : ℝ) ≤ y from hxy])
    have := @lemma_approx_monotone_C1_I
    exact this ⟨f, by simpa using hf_cont⟩ hf_mono ε hε_pos
  refine ⟨fun x ↦ P ((x - a) / (b - a)), ?_, ?_, ?_⟩
  · simp_all only [MonotoneOn, Set.mem_Icc, and_imp, gt_iff_lt, Subtype.forall]
    refine hP_cont.comp (ContDiffOn.div_const (contDiffOn_id.sub contDiffOn_const) _)
      fun x hx ↦ ⟨?_, ?_⟩ <;> nlinarith [hx.1, hx.2, mul_div_cancel₀ (x - a) (sub_ne_zero_of_ne hab.ne')]
  · simp_all only [MonotoneOn, Set.mem_Icc, and_imp, gt_iff_lt, Subtype.forall]
    exact fun x hx₁ hx₂ y hy₁ hy₂ hxy ↦ hP_mono (div_nonneg (by linarith) (by linarith))
      (div_le_one_of_le₀ (by linarith) (by linarith)) (div_nonneg (by linarith) (by linarith))
        (div_le_one_of_le₀ (by linarith) (by linarith)) (div_le_div_of_nonneg_right (by linarith) (by linarith))
  · simp_all only [MonotoneOn, Set.mem_Icc, and_imp, gt_iff_lt, Subtype.forall]
    intro x hx₁ hx₂
    convert hP_approx ((x - a) / (b - a)) (div_nonneg (by linarith) (by linarith))
      (div_le_one_of_le₀ (by linarith) (by linarith)) using 1
    congr 1
    rw [div_mul_cancel₀ _ (by linarith)]
    ring_nf

/-- Integration by parts bound for continuous monotone functions.
For continuous monotone `g` and `C¹` `F`, `‖∫ g F' - [gF]‖ ≤ sup ‖F‖ · (g(b) - g(a))`. -/
private theorem lemma_IBP_bound_monotone {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hg_cont : ContinuousOn g (Icc a b))
    (hg_mono : MonotoneOn g (Icc a b))
    (hF_C1 : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
    (⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a) := by
  have happrox := lemma_approx_monotone_C1 hab g hg_cont hg_mono
  choose! g' hg'_cont hg'_mono hg'_approx using happrox
  let gₙ := fun (n : ℕ) ↦ g' (1 / (n + 1 : ℝ))
  have hpos : ∀ n : ℕ, 0 < (1 : ℝ) / (n + 1) := fun n ↦ by positivity
  have hgₙ_cont : ∀ n, ContDiffOn ℝ 1 (gₙ n) (Icc a b) := fun n ↦ hg'_cont _ (hpos n)
  have hgₙ_mono : ∀ n, MonotoneOn (gₙ n) (Icc a b) := fun n ↦ hg'_mono _ (hpos n)
  have hgₙ_bound : ∀ n, ∀ x ∈ Icc a b, |gₙ n x - g x| ≤ 1 / (n + 1 : ℝ) := fun n x hx ↦ by
    rw [abs_sub_comm]; exact (hg'_approx _ (hpos n) x hx).le
  have hgₙ_lim : ∀ x ∈ Icc a b, Tendsto (fun n ↦ gₙ n x) atTop (nhds (g x)) := fun x hx ↦ by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ ↦ by positivity) (fun n ↦ hgₙ_bound n x hx)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hboundₙ : ∀ n, ‖(∫ t in Icc a b, (gₙ n t : ℂ) * deriv F t) - (gₙ n b * F b - gₙ n a * F a)‖ ≤
      (⨆ t ∈ Icc a b, ‖F t‖) * (gₙ n b - gₙ n a) := fun n ↦ by
    convert lemma_IBP_bound_C1_monotone hab (gₙ n) F (hgₙ_cont n) (hgₙ_mono n) hF_C1 using 1
  have hconv : Tendsto (fun n ↦ ∫ t in Icc a b, (gₙ n t : ℂ) * deriv F t) atTop
      (nhds (∫ t in Icc a b, (g t : ℂ) * deriv F t)) := by
    let M := sSup (image (|g ·|) (Icc a b))
    have hM_bdd : BddAbove (image (|g ·|) (Icc a b)) :=
      IsCompact.bddAbove (isCompact_Icc.image_of_continuousOn (continuous_abs.comp_continuousOn hg_cont))
    have hM : ∀ x ∈ Icc a b, |g x| ≤ M := fun x hx ↦ le_csSup hM_bdd (mem_image_of_mem _ hx)
    refine tendsto_integral_of_dominated_convergence (fun x ↦ (M + 1) * ‖deriv F x‖) ?_ ?_ ?_ ?_
    · exact fun n ↦ AEStronglyMeasurable.mul (ContinuousOn.aestronglyMeasurable
        (continuous_ofReal.comp_continuousOn (hgₙ_cont n).continuousOn) measurableSet_Icc) (by fun_prop)
    · apply Integrable.const_mul <| Integrable.norm <|
        (hF_C1.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl).integrableOn_Icc.congr _
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Icc]
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp (measure_singleton a),
        measure_eq_zero_iff_ae_notMem.mp (measure_singleton b)] with x hxa hxb hx
      rw [derivWithin_of_mem_nhds]
      exact Icc_mem_nhds (lt_of_le_of_ne hx.1 (fun h ↦ hxa (mem_singleton_iff.mpr h.symm)))
        (lt_of_le_of_ne hx.2 hxb)
    · intro n
      filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      simp only [norm_mul]; gcongr; norm_cast
      calc |gₙ n x| = ‖gₙ n x‖ := (norm_eq_abs _).symm
        _ = ‖(gₙ n x - g x) + g x‖ := by rw [sub_add_cancel]
        _ ≤ ‖gₙ n x - g x‖ + ‖g x‖ := norm_add_le _ _
        _ = |gₙ n x - g x| + |g x| := by simp only [norm_eq_abs]
        _ ≤ 1 / ((n : ℝ) + 1) + M := add_le_add (hgₙ_bound n x hx) (hM x hx)
        _ ≤ 1 + M := by gcongr; rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
        _ = M + 1 := add_comm ..
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
      exact Tendsto.mul (continuous_ofReal.continuousAt.tendsto.comp <| hgₙ_lim x hx)
        tendsto_const_nhds
  have hlim_lhs : Tendsto (fun n ↦ ‖(∫ t in Icc a b, (gₙ n t : ℂ) * deriv F t) -
      (gₙ n b * F b - gₙ n a * F a)‖) atTop
      (nhds ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖) := by
    refine Tendsto.norm <| Tendsto.sub hconv <| Tendsto.sub ?_ ?_
    · exact Tendsto.mul (continuous_ofReal.continuousAt.tendsto.comp
        (hgₙ_lim b (right_mem_Icc.mpr hab.le))) tendsto_const_nhds
    · exact Tendsto.mul (continuous_ofReal.continuousAt.tendsto.comp
        (hgₙ_lim a (left_mem_Icc.mpr hab.le))) tendsto_const_nhds
  have hlim_rhs : Tendsto (fun n ↦ (⨆ t ∈ Icc a b, ‖F t‖) * (gₙ n b - gₙ n a)) atTop
      (nhds ((⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a))) := by
    exact Tendsto.mul tendsto_const_nhds
      (Tendsto.sub (hgₙ_lim b (right_mem_Icc.mpr hab.le)) (hgₙ_lim a (left_mem_Icc.mpr hab.le)))
  exact le_of_tendsto_of_tendsto' hlim_lhs hlim_rhs hboundₙ

/-- Integration by parts bound for continuous functions with antitone absolute value.
If `|g|` is antitone, `‖∫ g F'‖ ≤ sup ‖F‖ · 2 |g(a)|`. -/
private theorem lemma_IBP_bound_abs_antitone {a b : ℝ} (hab : a < b) (g : ℝ → ℝ) (F : ℝ → ℂ)
    (hgcont : ContinuousOn g (Icc a b)) (hganti : AntitoneOn (|g ·|) (Icc a b))
    (hF : ContDiffOn ℝ 1 F (Icc a b)) :
    ‖∫ t in Icc a b, (g t : ℂ) * deriv F t‖ ≤ (⨆ t ∈ Icc a b, ‖F t‖) * (2 * |g a|) := by
  have hsign : (∀ t ∈ Icc a b, g t ≥ 0) ∨ (∀ t ∈ Icc a b, g t ≤ 0) := by
    by_cases hsign : ∃ a' b' : ℝ, a ≤ a' ∧ a' < b' ∧ b' ≤ b ∧ g a' * g b' < 0
    · obtain ⟨a', b', ha', hb', hab', hsign⟩ := hsign
      obtain ⟨r, hr⟩ : ∃ r ∈ Icc a' b', g r = 0 := by
        have hivt : ContinuousOn g (Icc a' b') := hgcont.mono (Icc_subset_Icc ha' hab')
        have := hivt.image_Icc hb'.le
        exact this.symm.subset (Set.mem_Icc.mpr ⟨by nlinarith [Set.mem_Icc.mp (this ▸
          mem_image_of_mem g (Set.left_mem_Icc.mpr hb'.le)), Set.mem_Icc.mp (this ▸
          mem_image_of_mem g (Set.right_mem_Icc.mpr hb'.le))], by nlinarith [mem_Icc.mp (this ▸
          mem_image_of_mem g (Set.left_mem_Icc.mpr hb'.le)), mem_Icc.mp (this ▸
          mem_image_of_mem g (Set.right_mem_Icc.mpr hb'.le))]⟩)
      have := hganti ⟨by linarith [hr.1.1], by linarith [hr.1.2]⟩ ⟨by linarith [hr.1.1], by
        linarith [hr.1.2]⟩ hr.1.2
      simp_all
    · contrapose! hsign
      obtain ⟨⟨x, hx₁, hx₂⟩, ⟨y, hy₁, hy₂⟩⟩ := hsign
      norm_num at *
      cases lt_or_gt_of_ne (show x ≠ y by rintro rfl; linarith) with
      | inl h => exact ⟨x, hx₁.1, y, by linarith, by linarith, by nlinarith⟩
      | inr h => exact ⟨y, hy₁.1, x, by linarith, by linarith, by nlinarith⟩
  cases hsign with
  | inl hsign =>
    have hbd₁ : ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
        (⨆ t ∈ Icc a b, ‖F t‖) * (g a - g b) := by
      have := @lemma_IBP_bound_monotone a b hab (fun t ↦ -g t) F ?_ ?_ ?_ <;> norm_num at *
      · convert this using 1 <;> norm_num [integral_neg]
        · ring_nf; rw [← norm_neg]; ring_nf
        · exact Or.inl <| by ring
      · exact hgcont.neg
      · intro t ht u hu htu; have := hganti ht hu htu; simp_all [abs_of_nonneg]
      · assumption
    have hbd₂ : ‖g b * F b - g a * F a‖ ≤ (⨆ t ∈ Icc a b, ‖F t‖) * (g b + g a) := by
      refine (norm_sub_le _ _).trans ?_
      have hFle : ∀ t ∈ Icc a b, ‖F t‖ ≤ ⨆ t ∈ Icc a b, ‖F t‖ := fun t ht ↦ by
        apply le_csSup
        · obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hF.continuousOn
          exact ⟨max M 1, forall_mem_range.mpr fun t ↦ by rw [ciSup_eq_ite]; aesop⟩
        · exact ⟨t, by simp_all⟩
      norm_num at *
      rw [abs_of_nonneg (hsign b hab.le le_rfl), abs_of_nonneg (hsign a le_rfl hab.le)]
      nlinarith [hFle b hab.le le_rfl, hFle a le_rfl hab.le, hsign b hab.le le_rfl, hsign a le_rfl hab.le]
    have hbd₃ : ‖∫ t in Icc a b, (g t : ℂ) * deriv F t‖ ≤
        (⨆ t ∈ Icc a b, ‖F t‖) * (g a - g b) + (⨆ t ∈ Icc a b, ‖F t‖) * (g b + g a) := by
      have h := norm_add_le ((∫ t in Icc a b, (g t : ℂ) * deriv F t) -
        (g b * F b - g a * F a)) (g b * F b - g a * F a)
      simpa using h.trans (add_le_add hbd₁ hbd₂)
    exact hbd₃.trans (by
      rw [abs_of_nonneg (hsign a <| left_mem_Icc.mpr hab.le)]
      nlinarith [show 0 ≤ ⨆ t ∈ Icc a b, ‖F t‖ from iSup_nonneg fun _ ↦ iSup_nonneg fun _ ↦ norm_nonneg _])
  | inr hsign =>
    have hbd₁ : ‖(∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)‖ ≤
        (⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a) := by
      apply_rules [lemma_IBP_bound_monotone]
      intro x hx y hy hxy; have := hganti hx hy hxy; simp_all [abs_of_nonpos]
    have hbd₂ : ‖g b * F b - g a * F a‖ ≤ (⨆ t ∈ Icc a b, ‖F t‖) * (|g b| + |g a|) := by
      have hFle : ∀ t ∈ Icc a b, ‖F t‖ ≤ ⨆ t ∈ Icc a b, ‖F t‖ := fun t ht ↦ by
        apply le_csSup
        · obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn isCompact_Icc hF.continuousOn.norm
          use max M 1
          rintro x ⟨t, rfl⟩; by_cases ht : t ∈ Icc a b <;> simp_all
        · exact ⟨t, by simp_all⟩
      refine (norm_sub_le ..).trans ?_
      simp only [Set.mem_Icc, and_imp, norm_mul, norm_real, norm_eq_abs] at *
      nlinarith [abs_nonneg (g b), abs_nonneg (g a),
        hFle b (by linarith) (by linarith), hFle a (by linarith) (by linarith)]
    have hbd₃ : ‖∫ t in Icc a b, (g t : ℂ) * deriv F t‖ ≤
        (⨆ t ∈ Icc a b, ‖F t‖) * (g b - g a) + (⨆ t ∈ Icc a b, ‖F t‖) * (|g b| + |g a|) := by
      have h := norm_add_le ((∫ t in Icc a b, (g t : ℂ) * deriv F t) - (g b * F b - g a * F a)) (g b * F b - g a * F a)
      simpa using h.trans (add_le_add hbd₁ hbd₂)
    convert hbd₃ using 1
    rw [abs_of_nonpos (hsign b <| right_mem_Icc.mpr hab.le), abs_of_nonpos (hsign a <| left_mem_Icc.mpr hab.le)]
    ring

set_option backward.isDefEq.respectTransparency false in

private theorem lemma_aachmonophase {a b : ℝ} (ha : a < b) (φ : ℝ → ℝ) (hφ_C1 : ContDiffOn ℝ 1 φ (Set.Icc a b))
    (hφ'_ne0 : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0) (h g : ℝ → ℝ) (hg : ∀ t, g t = h t / deriv φ t)
    (hg_cont : ContinuousOn g (Set.Icc a b)) (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b)) :
    ‖∫ t in Set.Icc a b, h t * e (φ t)‖ ≤ |g a| / π := by
  let F : ℝ → ℂ := fun t ↦ (1 / (2 * Real.pi * I)) * (exp (2 * Real.pi * I * φ t))
  have h_integral_bound : ‖∫ t in Set.Icc a b, (g t : ℂ) * (deriv F t)‖ ≤ (⨆ t ∈ Set.Icc a b, ‖F t‖) * (2 * |g a|) :=
    lemma_IBP_bound_abs_antitone ha g F hg_cont hg_mon <|
      ContDiffOn.mul contDiffOn_const <| contDiff_exp.comp_contDiffOn <|
        ContDiffOn.mul contDiffOn_const <| ofRealCLM.contDiff.comp_contDiffOn hφ_C1
  have h_deriv_F : ∀ t ∈ Set.Ioo a b, deriv F t = (exp (2 * Real.pi * I * φ t)) * (deriv φ t) := by
    intro t ht
    rw [deriv_const_mul]
    · norm_num [Complex.exp_ne_zero, mul_comm]
      erw [HasDerivAt.deriv (HasDerivAt.comp t (Complex.hasDerivAt_exp _) (HasDerivAt.mul (HasDerivAt.ofReal_comp
        (hφ_C1.differentiableOn_one |> DifferentiableOn.hasDerivAt <| Icc_mem_nhds ht.1 ht.2)) <| hasDerivAt_const ..))]
      norm_num
      ring_nf
      simp
    · apply Complex.differentiableAt_exp.comp
      apply DifferentiableAt.const_mul <| ofRealCLM.differentiableAt.comp _ <| DifferentiableOn.differentiableAt
        hφ_C1.differentiableOn_one (Icc_mem_nhds ht.1 ht.2) ..
  have h_norm_F : ⨆ t ∈ Set.Icc a b, ‖F t‖ = 1 / (2 * Real.pi) := by
    dsimp only [F]
    rw [@ciSup_eq_of_forall_le_of_forall_lt_exists_gt] <;> norm_num [norm_exp, abs_of_nonneg pi_pos.le]
    · exact fun t ↦ by rw [ciSup_eq_ite]; split_ifs <;> norm_num; linarith [pi_pos]
    · exact fun w hw ↦ ⟨a, hw.trans_le <| by rw [ciSup_pos]; norm_num; linarith⟩
  have h_integral_subst : ‖∫ t in Set.Icc a b, (g t : ℂ) * (deriv F t)‖ = ‖∫ t in Set.Icc a b,
      (h t : ℂ) * (exp (2 * Real.pi * I * φ t))‖ := by
    simp only [integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
    rw [setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ by rw [h_deriv_F t ht, hg t]]
    simp only [div_eq_mul_inv, ofReal_mul, ofReal_inv, mul_comm, mul_left_comm, mul_assoc]
    refine congr_arg Norm.norm <| setIntegral_congr_fun measurableSet_Ioo <| fun x hx ↦ ?_
    simp [mul_inv_cancel_left₀ (ofReal_ne_zero.mpr (hφ'_ne0 x (Set.Ioo_subset_Icc_self hx)))]
  exact h_integral_subst ▸ h_integral_bound.trans (by rw [h_norm_F]; ring_nf; norm_num [pi_pos.ne'])

/-- Public form of the non-stationary phase estimate used in the sharp-zeta
Poisson argument.  This wrapper exposes the proved first-derivative test
without exposing the appendix's private notation `e`. -/
theorem nonstationary_phase_integral_bound {a b : ℝ} (ha : a < b)
    (φ : ℝ → ℝ) (hφ_C1 : ContDiffOn ℝ 1 φ (Set.Icc a b))
    (hφ'_ne0 : ∀ t ∈ Set.Icc a b, deriv φ t ≠ 0)
    (h g : ℝ → ℝ) (hg : ∀ t, g t = h t / deriv φ t)
    (hg_cont : ContinuousOn g (Set.Icc a b))
    (hg_mon : AntitoneOn (fun t ↦ |g t|) (Set.Icc a b)) :
    ‖∫ t in Set.Icc a b,
        (h t : ℂ) * Complex.exp (2 * Real.pi * I * (φ t : ℂ))‖ ≤
      |g a| / Real.pi := by
  simpa only [e] using
    lemma_aachmonophase ha φ hφ_C1 hφ'_ne0 h g hg hg_cont hg_mon

end ZetaAppendix
