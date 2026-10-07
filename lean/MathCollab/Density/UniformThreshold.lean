module
public import MathCollab.Density.DivisorGrowth
public import MathCollab.Density.BootstrapAbsorption
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

open Real Set Filter
open scoped BigOperators Topology

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

theorem LargeValueData.scalar_square_le {κ : ℝ} (d : LargeValueData κ) :
    (d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2 ≤
      (divisorMaximum d.T : ℝ)^2*(d.N : ℝ)^(-4*κ) := by
  have hN : (0 : ℝ) < d.N := by exact_mod_cast d.N_pos
  have hV := d.V_pos
  have hp : (d.N : ℝ)^3*(d.N : ℝ)^(4*κ) ≤ d.V^4 := by
    have he : (d.N : ℝ)^3*(d.N : ℝ)^(4*κ) = ((d.N : ℝ)^(3/4+κ))^4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hN, ← Real.rpow_natCast,
        ← Real.rpow_mul hN.le]
      congr 1
      ring
    rw [he]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hN.le _) d.height 4
  calc
    _ = (divisorMaximum d.T : ℝ)^2*(d.N : ℝ)^3/d.V^4 := by unfold bootstrapScalar; ring
    _ ≤ (divisorMaximum d.T : ℝ)^2/(d.N : ℝ)^(4*κ) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      have hh := mul_le_mul_of_nonneg_left hp (sq_nonneg (divisorMaximum d.T : ℝ))
      nlinarith
    _ = _ := by rw [show -4*κ = -(4*κ) by ring, Real.rpow_neg hN.le]; ring

/-- eta=kappa/6 is chosen before every configuration. -/
theorem uniform_scalar_decay {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ d : LargeValueData κ,
      (d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2 ≤ C*d.T^(-κ) := by
  obtain ⟨C, hC, hd⟩ := divisorMaximum_subpower (show 0 < κ/6 by positivity)
  refine ⟨C^2, by nlinarith, ?_⟩
  intro d
  have hT : 0 < d.T := by linarith [d.T_ge_two]
  have hN : (0 : ℝ) < d.N := by exact_mod_cast d.N_pos
  have hp : (d.N : ℝ)^(-4*κ) ≤ d.T^(-4*κ/3) := by
    have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hT _) d.scale_lower
      (show -4*κ ≤ 0 by linarith)
    have he : (d.T^(1/3 : ℝ))^(-4*κ) = d.T^(-4*κ/3) := by
      rw [← Real.rpow_mul hT.le]
      congr 1
      ring
    exact hh.trans_eq he
  have hdelta := pow_le_pow_left₀ (Nat.cast_nonneg (divisorMaximum d.T)) (hd d.T d.T_ge_two) 2
  calc
    _ ≤ (divisorMaximum d.T : ℝ)^2*(d.N : ℝ)^(-4*κ) := d.scalar_square_le
    _ ≤ (C*d.T^(κ/6))^2*d.T^(-4*κ/3) :=
      mul_le_mul hdelta hp (Real.rpow_nonneg hN.le _) (sq_nonneg _)
    _ = C^2*d.T^(-κ) := by
      rw [mul_pow, ← Real.rpow_natCast (d.T^(κ/6)) 2, ← Real.rpow_mul hT.le, mul_assoc, ← Real.rpow_add hT]
      congr 1
      congr 1
      ring

theorem tendsto_power_log_two_mul {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun T : ℝ => T^(-κ)*Real.log (2*T)) atTop (𝓝 0) := by
  have hp := tendsto_rpow_neg_atTop hκ
  have hl := (isLittleO_log_rpow_atTop hκ).tendsto_div_nhds_zero
  have hh := (hp.mul_const (Real.log 2)).add hl
  simp only [zero_mul, zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne', Real.rpow_neg hT.le]
  ring

/-- The threshold is chosen before T,N,V,a,W,t0, not separately for each configuration. -/
theorem uniform_absorption_threshold {κ : ℝ} (hκ : 0 < κ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ d : LargeValueData κ, T₀ ≤ d.T →
      A*(d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2*Real.log (2*d.T) ≤ 1/2 ∧
      (d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2 ≤ 1 := by
  obtain ⟨C, hC, hc⟩ := uniform_scalar_decay hκ
  have hplain : Tendsto (fun T : ℝ => C*T^(-κ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hκ).const_mul C
  have hlog : Tendsto (fun T : ℝ => A*C*(T^(-κ)*Real.log (2*T))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_power_log_two_mul hκ).const_mul (A*C)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (hplain.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (hlog.eventually_lt_const (by norm_num : (0 : ℝ) < 1/2))
  refine ⟨max 2 (max T₁ T₂), le_max_left _ _, ?_⟩
  intro d hT
  have ht₁ : T₁ ≤ d.T := (le_max_left T₁ T₂).trans ((le_max_right 2 _).trans hT)
  have ht₂ : T₂ ≤ d.T := (le_max_right T₁ T₂).trans ((le_max_right 2 _).trans hT)
  have hlogpos : 0 ≤ Real.log (2*d.T) := Real.log_nonneg (by linarith [d.T_ge_two])
  constructor
  · have hh := mul_le_mul_of_nonneg_left (hc d) (mul_nonneg hA hlogpos)
    have hi := (hT₂ d.T ht₂).le
    nlinarith
  · exact (hc d).trans (hT₁ d.T ht₁).le

/-- The kernel constant and large-T threshold are uniform in every original configuration. -/
theorem uniform_absorbed_kernel (w : ComparisonCutoff) {κ : ℝ} (hκ : 0 < κ) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 2 ≤ T₀ ∧ ∀ d : LargeValueData κ, d.W.Nonempty → T₀ ≤ d.T →
      (d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2 ≤ 1 ∧
      ∀ (U : Finset ℝ) (L : ℝ), U ⊆ d.W → (d.N : ℝ) ≤ L → L ≤ 8*(d.T+1) →
        kernelEnergy w.toReflectionCutoff L U ≤ C*bootstrapScalar d.T d.N d.V*U.card*
          (L^2+(d.N : ℝ)*localDiameter U) := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hbound⟩ := bootstrap_absorbed w
  obtain ⟨T₀, hT₀, hsmall⟩ := uniform_absorption_threshold hκ C₁ hC₁
  refine ⟨2*C₀, T₀, by positivity, hT₀, ?_⟩
  intro d hW hT
  obtain ⟨hs, hs'⟩ := hsmall d hT
  have hB := hbound d hW hs
  refine ⟨hs', ?_⟩
  intro U L hU hL hL'
  by_cases hn : U.Nonempty
  · have hQ := kernelEnergy_le_bootstrapBound w.toReflectionCutoff d
      (mem_bootstrapFamily.mpr ⟨hU, hn⟩) ⟨hL, hL'⟩
    have hb := bootstrapScalar_nonneg d.T d.V d.N
    have hd := localDiameter_ge_one U
    calc
      _ ≤ bootstrapBound w.toReflectionCutoff d * bootstrapScalar d.T d.N d.V * U.card *
          (L^2+(d.N : ℝ)*localDiameter U) := hQ
      _ ≤ _ := by gcongr
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, kernelEnergy, Finset.sum_empty,
      Finset.card_empty, Nat.cast_zero, mul_zero, zero_mul, le_refl]

end MathCollab.Density
