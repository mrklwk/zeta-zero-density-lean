module
public import MathCollab.Density.CutoffTransforms

@[expose] public section

open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff

noncomputable section
namespace MathCollab.Density

def retainedMode (w : ℝ → ℂ) (L H v : ℝ) (m : ℤ) : ℂ :=
  if inReflectionBand L H m then modeIntegral w v ((m : ℝ) * L) else 0

/-- A finite representation of the exact integer band. -/
def reflectionBand (L H : ℝ) : Finset ℤ :=
  (Finset.Icc 1 ⌈4 * H / (Real.pi * L)⌉).filter (inReflectionBand L H)

theorem mem_reflectionBand (L H : ℝ) (m : ℤ) :
    m ∈ reflectionBand L H ↔ inReflectionBand L H m := by
  constructor
  · intro hm
    exact (Finset.mem_filter.mp hm).2
  · intro hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by have := hm.1; omega, ?_⟩, hm⟩
    have hh := hm.2.2.trans (Int.le_ceil (4 * H / (Real.pi * L)))
    exact_mod_cast hh

theorem tsum_retainedMode_eq_finite (w : ℝ → ℂ) (L H v : ℝ) :
    (∑' m : ℤ, retainedMode w L H v m) =
      ∑ m ∈ reflectionBand L H, modeIntegral w v ((m : ℝ) * L) := by
  rw [tsum_eq_sum (s := reflectionBand L H) (fun m hm => by
    simp only [retainedMode, ite_eq_right (fun h => hm ((mem_reflectionBand L H m).2 h))])]
  apply Finset.sum_congr rfl
  intro m hm
  exact ite_eq_left ((mem_reflectionBand L H m).1 hm)

def bandContribution (w : ReflectionCutoff) (L H v : ℝ) : ℂ :=
  (L : ℂ) * ∑' m : ℤ, retainedMode (fun x => (w x : ℂ)) L H v m

theorem summable_retainedMode (w : ReflectionCutoff) {L : ℝ} (hL : 0 < L) (H v : ℝ) :
    Summable (retainedMode (fun x => (w x : ℂ)) L H v) := by
  apply (summable_modeIntegral w.complex_smooth w.complex_support hL v).norm.of_norm_bounded
    (f := retainedMode (fun x => (w x : ℂ)) L H v)
  intro m
  unfold retainedMode
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using
      norm_nonneg (modeIntegral (fun x => (w x : ℂ)) v ((m : ℝ) * L))

theorem summable_discardedMode (w : ReflectionCutoff) {L : ℝ} (hL : 0 < L) (H v : ℝ) :
    Summable (discardedMode (fun x => (w x : ℂ)) L H v) := by
  apply (summable_modeIntegral w.complex_smooth w.complex_support hL v).norm.of_norm_bounded
    (f := discardedMode (fun x => (w x : ℂ)) L H v)
  intro m
  unfold discardedMode
  split_ifs
  · exact le_rfl
  · simpa only [norm_zero] using
      norm_nonneg (modeIntegral (fun x => (w x : ℂ)) v ((m : ℝ) * L))

theorem nonzeroMode_eq_retained_add_discarded (w : ℝ → ℂ) (L H v : ℝ) (m : ℤ) :
    nonzeroMode w L v m = retainedMode w L H v m + discardedMode w L H v m := by
  unfold nonzeroMode retainedMode discardedMode
  by_cases hm : m = 0
  · subst m
    have hnot : ¬inReflectionBand L H 0 := by intro h; exact lt_irrefl 0 h.1
    simp only [hnot, ↓reduceIte, ne_eq, not_true_eq_false, false_and, add_zero]
  · by_cases hb : inReflectionBand L H m <;> simp [hm, hb]

/-- Exact fixed-band decomposition of h_L, before any estimate. -/
theorem hKernel_sub_bandContribution (w : ReflectionCutoff) {L : ℝ} (hL : 0 < L) (H v : ℝ) :
    hKernel w L v - bandContribution w L H v =
      (L : ℂ) * ∑' m : ℤ, discardedMode (fun x => (w x : ℂ)) L H v m := by
  rw [hKernel_poisson w hL, bandContribution]
  simp_rw [nonzeroMode_eq_retained_add_discarded (fun x => (w x : ℂ)) L H v]
  rw [(summable_retainedMode w hL H v).tsum_add (summable_discardedMode w hL H v)]
  ring

/-- Uniform fixed-band error and diagonal error share one cutoff/order constant. -/
theorem uniform_fixedBand_and_diagonal_error (w : ReflectionCutoff) {A : ℕ} (hA : 1 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L H v : ℝ, 0 < L → 0 < H → H ≤ v → v ≤ 2 * H →
      ‖hKernel w L v - bandContribution w L H v‖ ≤ K * L / L ^ A ∧
      ‖hKernel w L 0‖ ≤ K * L / L ^ A := by
  obtain ⟨K₁, hK₁, hb⟩ := uniform_discarded_modes w.complex_smooth w.complex_support hA
  obtain ⟨K₂, hK₂, hz⟩ := uniform_zero_modes w.complex_smooth w.complex_support hA
  refine ⟨max K₁ K₂, hK₁.trans (le_max_left _ _), ?_⟩
  intro L H v hL hH hv hv2
  constructor
  · rw [hKernel_sub_bandContribution w hL]
    refine (hb L H v hL hH hv hv2).2.trans ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left K₁ K₂) hL.le) (pow_nonneg hL.le A)
  · rw [hKernel_poisson w hL]
    refine (hz L hL).2.trans ?_
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right K₁ K₂) hL.le) (pow_nonneg hL.le A)

end MathCollab.Density
