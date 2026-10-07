module
public import MathCollab.Density.BootstrapDomain
public import MathCollab.Density.ComparisonExpansion

@[expose] public section

open Real Complex Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- A crude bound used only to establish finiteness, before any bootstrap inequality. -/
theorem crude_kernel_bound (w : ReflectionCutoff) {B : ℝ} (hB : 0 < B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ, 0 < L → L ≤ B → ∀ v : ℝ, ‖hKernel w L v‖ ≤ K := by
  have hs : HasCompactSupport w.toFun := isCompact_Icc.of_isClosed_subset (isClosed_tsupport w.toFun) w.support
  obtain ⟨C₀, hw⟩ := hs.exists_bound_of_continuous w.smooth.continuous
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (w 0)).trans (hw 0)
  obtain ⟨C₁, hC₁, hI⟩ := cutoffIntegral_quadratic_decay w
  refine ⟨(⌈5*B⌉₊+1 : ℕ)*C₀+B*C₁, by positivity, ?_⟩
  intro L hL hLB v
  have hIv : ‖cutoffIntegral w v‖ ≤ C₁ := (hI v).trans
    (div_le_self hC₁ (by nlinarith [abs_nonneg v]))
  have he : hKernel w L v =
      (∑ n ∈ Finset.range (⌈5*L⌉₊+1), (w ((n : ℝ)/L) : ℂ)*dirichletPhase ((n : ℝ)/L) v) -
        (L : ℂ)*cutoffIntegral w v := by
    rw [cutoff_finite_sum w hL]
    ring
  have hc : (⌈5*L⌉₊+1 : ℕ) ≤ ⌈5*B⌉₊+1 := Nat.add_le_add_right (Nat.ceil_mono (by linarith)) 1
  rw [he]
  calc
    _ ≤ ‖∑ n ∈ Finset.range (⌈5*L⌉₊+1),
        (w ((n : ℝ)/L) : ℂ)*dirichletPhase ((n : ℝ)/L) v‖ + ‖(L : ℂ)*cutoffIntegral w v‖ :=
      norm_sub_le _ _
    _ ≤ (⌈5*L⌉₊+1 : ℕ)*C₀ + L*C₁ := by
      apply add_le_add
      · apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑ _n ∈ Finset.range (⌈5*L⌉₊+1), C₀ := by
            apply Finset.sum_le_sum
            intro n hn
            simpa only [norm_mul, Complex.norm_real, norm_dirichletPhase, mul_one] using hw ((n : ℝ)/L)
          _ = _ := by simp
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
        exact mul_le_mul_of_nonneg_left hIv hL.le
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast hc) hC₀)
      (mul_le_mul_of_nonneg_right hLB hC₁)

def bootstrapValues (w : ReflectionCutoff) {κ : ℝ} (d : LargeValueData κ) : Set ℝ :=
  {x | ∃ U ∈ bootstrapFamily d.W, ∃ L ∈ Icc (d.N : ℝ) (8*(d.T+1)),
    x = kernelEnergy w L U /
      (bootstrapScalar d.T d.N d.V * U.card * (L^2+(d.N : ℝ)*localDiameter U))}

def bootstrapBound (w : ReflectionCutoff) {κ : ℝ} (d : LargeValueData κ) : ℝ :=
  sSup (bootstrapValues w d)

theorem bootstrapValues_nonempty (w : ReflectionCutoff) {κ : ℝ} (d : LargeValueData κ)
    (hW : d.W.Nonempty) : (bootstrapValues w d).Nonempty := by
  refine ⟨_, d.W, mem_bootstrapFamily.mpr ⟨Finset.Subset.refl _, hW⟩, (d.N : ℝ), ?_, rfl⟩
  exact ⟨le_rfl, by linarith [d.scale_upper, d.T_ge_two]⟩

theorem bootstrapValues_bddAbove (w : ReflectionCutoff) {κ : ℝ} (d : LargeValueData κ) :
    BddAbove (bootstrapValues w d) := by
  obtain ⟨K, hK, hk⟩ := crude_kernel_bound w (show 0 < 8*(d.T+1) by linarith [d.T_ge_two])
  refine ⟨(d.W.card : ℝ)^2*K^2, ?_⟩
  rintro x ⟨U, hU, L, hL, rfl⟩
  have hN : (0 : ℝ) < d.N := by exact_mod_cast d.N_pos
  have hLp : 0 < L := hN.trans_le hL.1
  have hn := d.normalization_lower hU hL.1
  have hN1 : (1 : ℝ) ≤ d.N := by exact_mod_cast d.N_pos
  have hden : 1 ≤ bootstrapScalar d.T d.N d.V * U.card * (L^2+(d.N : ℝ)*localDiameter U) := hN1.trans hn
  have hc : (U.card : ℝ) ≤ d.W.card := by
    exact_mod_cast Finset.card_le_card (mem_bootstrapFamily.mp hU).1
  calc
    _ ≤ kernelEnergy w L U := div_le_self (kernelEnergy_nonneg _ _ _) hden
    _ ≤ (U.card : ℝ)^2*K^2 := by
      calc
        _ ≤ ∑ _t ∈ U, ∑ _u ∈ U, K^2 := by
          apply Finset.sum_le_sum
          intro t ht
          apply Finset.sum_le_sum
          intro u hu
          exact pow_le_pow_left₀ (norm_nonneg _) (hk L hLp hL.2 (t-u)) 2
        _ = _ := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) (sq_nonneg _)

theorem bootstrapBound_nonneg (w : ReflectionCutoff) {κ : ℝ} (d : LargeValueData κ)
    (hW : d.W.Nonempty) : 0 ≤ bootstrapBound w d := by
  obtain ⟨x, hx⟩ := bootstrapValues_nonempty w d hW
  have hle := le_csSup (bootstrapValues_bddAbove w d) hx
  obtain ⟨U, hU, L, hL, rfl⟩ := hx
  have hn := d.normalization_lower hU hL.1
  exact (div_nonneg (kernelEnergy_nonneg w L U)
    ((by exact_mod_cast d.N_pos.le : (0 : ℝ) ≤ d.N).trans hn)).trans hle

/-- The finite supremum bounds each descendant without assuming a kernel estimate. -/
theorem kernelEnergy_le_bootstrapBound (w : ReflectionCutoff) {κ : ℝ} (d : LargeValueData κ)
    {U : Finset ℝ} (hU : U ∈ bootstrapFamily d.W) {L : ℝ}
    (hL : L ∈ Icc (d.N : ℝ) (8*(d.T+1))) :
    kernelEnergy w L U ≤ bootstrapBound w d * bootstrapScalar d.T d.N d.V * U.card *
      (L^2+(d.N : ℝ)*localDiameter U) := by
  have hpos : 0 < bootstrapScalar d.T d.N d.V * U.card * (L^2+(d.N : ℝ)*localDiameter U) :=
    (by exact_mod_cast d.N_pos : (0 : ℝ) < d.N).trans_le (d.normalization_lower hU hL.1)
  have hh := le_csSup (bootstrapValues_bddAbove w d) (show
      kernelEnergy w L U /
        (bootstrapScalar d.T d.N d.V * U.card * (L^2+(d.N : ℝ)*localDiameter U)) ∈ bootstrapValues w d
      from ⟨U, hU, L, hL, rfl⟩)
  have hi := (div_le_iff₀ hpos).1 hh
  simpa only [bootstrapBound, mul_assoc] using hi

end MathCollab.Density
