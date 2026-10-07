module
public import MathCollab.Density.BootstrapShells

@[expose] public section

open Real Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- Uniform shell summation, retaining the local diameter and the logarithmic shell count. -/
theorem bootstrap_preabsorption (w : ComparisonCutoff) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ {κ : ℝ} (d : LargeValueData κ), d.W.Nonempty →
      ∀ (U : Finset ℝ) (L : ℝ), U ⊆ d.W → (d.N : ℝ) ≤ L →
      kernelEnergy w.toReflectionCutoff L U ≤
        2*C*bootstrapScalar d.T d.N d.V*(d.N : ℝ)*localDiameter U*U.card +
        C*bootstrapBound w.toReflectionCutoff d*(bootstrapScalar d.T d.N d.V)^3*U.card*
          (2*(d.N : ℝ)^2*localDiameter U+(d.N : ℝ)*L^2*(Real.log (2*d.T)/Real.log 2)) +
        E*d.T^(-90 : ℝ) := by
  obtain ⟨C, E, hC, hE, hshell⟩ := bootstrap_one_shell w
  obtain ⟨F, hF, hdiag⟩ := uniform_reflection_application w.toReflectionCutoff
  refine ⟨C, 2*E+F, hC, by positivity, ?_⟩
  intro κ d hW U L hU hL
  let b := bootstrapScalar d.T d.N d.V
  let B := bootstrapBound w.toReflectionCutoff d
  have hb : 0 ≤ b := bootstrapScalar_nonneg d.T d.V d.N
  have hB : 0 ≤ B := bootstrapBound_nonneg w.toReflectionCutoff d hW
  have hT : 0 < d.T := by linarith [d.T_ge_two]
  have hT1 : 1 ≤ d.T := by linarith [d.T_ge_two]
  have hsep := oneSeparated_subset d.separated hU
  have hd : localDiameter U ≤ d.T+1 := (d.local_card_le hU).2
  have hdiam : intervalSpan U ≤ d.T := by dsimp [localDiameter] at hd; linarith
  have hQ := kernelEnergy_le_dyadic_shells w.toReflectionCutoff L hsep
  have hdi := (hdiag d.T L 1 U d.T_ge_two (d.scale_lower.trans hL) (by norm_num) hsep hdiam).2
  have hs : (∑ k ∈ shellIndices U, shellEnergy w.toReflectionCutoff L ((2 : ℝ)^k) U) ≤
      2*C*b*(d.N : ℝ)*localDiameter U*U.card +
      C*B*b^3*U.card*(2*(d.N : ℝ)^2*localDiameter U+(d.N : ℝ)*L^2*(Real.log (2*d.T)/Real.log 2)) +
      E*((shellIndices U).card : ℝ)*d.T^(-100 : ℝ) := by
    have hp := Finset.sum_le_sum (s := shellIndices U) (fun k hk =>
      hshell d hW U L ((2 : ℝ)^k) hU hL (shellIndex_bounds hk).1
        ((shellIndex_bounds hk).2.trans hdiam))
    have heq : (∑ k ∈ shellIndices U,
        (C*b*(d.N : ℝ)*(2 : ℝ)^k*U.card +
          C*B*b^3*U.card*((d.N : ℝ)^2*(2 : ℝ)^k+(d.N : ℝ)*L^2) + E*d.T^(-100 : ℝ))) =
        C*b*(d.N : ℝ)*U.card*(∑ k ∈ shellIndices U, (2 : ℝ)^k) +
          C*B*b^3*U.card*((d.N : ℝ)^2*(∑ k ∈ shellIndices U, (2 : ℝ)^k)+
            (d.N : ℝ)*L^2*(shellIndices U).card) + E*(shellIndices U).card*d.T^(-100 : ℝ) := by
      simp_rw [mul_add]
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
        Finset.sum_const, nsmul_eq_mul]
      ring
    change (∑ k ∈ shellIndices U, shellEnergy w.toReflectionCutoff L ((2 : ℝ)^k) U) ≤ _ at hp
    rw [heq] at hp
    have hsum := shellIndices_sum_le U
    have hcard := shellIndices_card_le_log d.T_ge_two hdiam
    have hlead := mul_le_mul_of_nonneg_left hsum (show 0 ≤ C*b*(d.N : ℝ)*U.card by positivity)
    have hrec := mul_le_mul_of_nonneg_left hsum (show 0 ≤ C*B*b^3*U.card*(d.N : ℝ)^2 by positivity)
    have hlog := mul_le_mul_of_nonneg_left hcard (show 0 ≤ C*B*b^3*U.card*(d.N : ℝ)*L^2 by positivity)
    nlinarith
  have hcardT : ((shellIndices U).card : ℝ) ≤ 2*d.T := (shellIndices_card_le_diameter U).trans (by linarith)
  have he : d.T*d.T^(-100 : ℝ) = d.T^(-99 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one d.T]
    rw [← Real.rpow_add hT]
    norm_num
  have hpow : d.T^(-99 : ℝ) ≤ d.T^(-90 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have hpow' : d.T^(-100 : ℝ) ≤ d.T^(-90 : ℝ) := Real.rpow_le_rpow_of_exponent_le hT1 (by norm_num)
  have herr₁ : E*((shellIndices U).card : ℝ)*d.T^(-100 : ℝ) ≤ 2*E*d.T^(-90 : ℝ) := by
    calc
      _ ≤ E*(2*d.T)*d.T^(-100 : ℝ) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcardT hE) (Real.rpow_nonneg hT.le _)
      _ = 2*E*(d.T*d.T^(-100 : ℝ)) := by ring
      _ ≤ _ := by rw [he]; exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have herr₂ := mul_le_mul_of_nonneg_left hpow' hF
  dsimp [b, B] at hs
  linarith

/-- Scalar absorption with the precise Nb² log(2T) coefficient and constants before all data. -/
theorem bootstrap_absorption_inequality (w : ComparisonCutoff) :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ {κ : ℝ} (d : LargeValueData κ), d.W.Nonempty →
      bootstrapBound w.toReflectionCutoff d ≤ C₀ +
        C₁*(d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2*Real.log (2*d.T)*bootstrapBound w.toReflectionCutoff d := by
  obtain ⟨C, E, hC, hE, hpre⟩ := bootstrap_preabsorption w
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨2*C+E, 2*C/Real.log 2, by positivity, by positivity, ?_⟩
  intro κ d hW
  apply csSup_le (bootstrapValues_nonempty w.toReflectionCutoff d hW)
  rintro x ⟨U, hU, L, hL, rfl⟩
  let b := bootstrapScalar d.T d.N d.V
  let B := bootstrapBound w.toReflectionCutoff d
  let D := b*U.card*(L^2+(d.N : ℝ)*localDiameter U)
  let ℓ := Real.log (2*d.T)/Real.log 2
  have hb : 0 ≤ b := bootstrapScalar_nonneg d.T d.V d.N
  have hB : 0 ≤ B := bootstrapBound_nonneg w.toReflectionCutoff d hW
  have hN : (0 : ℝ) < d.N := by exact_mod_cast d.N_pos
  have hD : 1 ≤ D := (by exact_mod_cast d.N_pos : (1 : ℝ) ≤ d.N).trans (d.normalization_lower hU hL.1)
  have hDp : 0 < D := by linarith
  have hℓ : 1 ≤ ℓ := (le_div_iff₀ hlog2).2 (by
    simpa only [one_mul] using Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith [d.T_ge_two] : 2 ≤ 2*d.T))
  have hp := hpre d hW U L (mem_bootstrapFamily.mp hU).1 hL.1
  have hlead : 2*C*b*(d.N : ℝ)*localDiameter U*U.card ≤ 2*C*D := by
    have hh := mul_nonneg (show 0 ≤ 2*C*b*U.card by positivity) (sq_nonneg L)
    dsimp [D]
    nlinarith
  have hinner : 2*(d.N : ℝ)^2*localDiameter U+(d.N : ℝ)*L^2*ℓ ≤
      2*ℓ*(d.N : ℝ)*(L^2+(d.N : ℝ)*localDiameter U) := by
    have hd := localDiameter_ge_one U
    have hh := mul_nonneg (show 0 ≤ ℓ-1 by linarith)
      (show 0 ≤ (d.N : ℝ)^2*localDiameter U by positivity)
    have hi := mul_nonneg (show 0 ≤ ℓ by linarith) (show 0 ≤ (d.N : ℝ)*L^2 by positivity)
    nlinarith
  have hrec := mul_le_mul_of_nonneg_left hinner (show 0 ≤ C*B*b^3*U.card by positivity)
  have hpow : d.T^(-90 : ℝ) ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by linarith [d.T_ge_two] : 1 ≤ d.T)
      (by norm_num : (-90 : ℝ) ≤ 0)
    simpa only [Real.rpow_zero] using hh
  have he₀ : E*1 ≤ E*D := mul_le_mul_of_nonneg_left hD hE
  have he : E*d.T^(-90 : ℝ) ≤ E*D := (mul_le_mul_of_nonneg_left hpow hE).trans he₀
  change kernelEnergy w.toReflectionCutoff L U / D ≤ _
  apply (div_le_iff₀ hDp).2
  have hrewrite : (2*C/Real.log 2)*(d.N : ℝ)*b^2*Real.log (2*d.T)*B*D =
      C*B*b^3*U.card*(2*ℓ*(d.N : ℝ)*(L^2+(d.N : ℝ)*localDiameter U)) := by
    dsimp [D, ℓ]
    ring
  dsimp [b, B, ℓ] at hrewrite hlead hrec he
  rw [add_mul]
  rw [hrewrite]
  dsimp [D, b] at he hlead ⊢
  nlinarith

/-- The remaining arithmetic threshold is exposed; no large-values conclusion is assumed. -/
theorem bootstrap_absorbed (w : ComparisonCutoff) :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ {κ : ℝ} (d : LargeValueData κ), d.W.Nonempty →
      C₁*(d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2*Real.log (2*d.T) ≤ 1/2 →
      bootstrapBound w.toReflectionCutoff d ≤ 2*C₀ := by
  obtain ⟨C₀, C₁, hC₀, hC₁, hbound⟩ := bootstrap_absorption_inequality w
  refine ⟨C₀, C₁, hC₀, hC₁, ?_⟩
  intro κ d hW hsmall
  have hB := bootstrapBound_nonneg w.toReflectionCutoff d hW
  have hh := hbound d hW
  have hi := mul_le_mul_of_nonneg_right hsmall hB
  nlinarith

end MathCollab.Density
