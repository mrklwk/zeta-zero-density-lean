module
public import MathCollab.Density.UniformThreshold

@[expose] public section

open Real Set
open scoped BigOperators

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Cardinality at an arbitrary admissible positive integer auxiliary scale. -/
theorem cardinality_at_length (w : ComparisonCutoff) {κ : ℝ} (d : LargeValueData κ)
    (hW : d.W.Nonempty) {K : ℝ} (hK : 0 ≤ K) {M : ℕ} (hM : 0 < M)
    (hscale : (d.N : ℝ)*M ≤ 8*(d.T+1))
    (hsmall : (d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2 ≤ 1)
    (hQ : kernelEnergy w.toReflectionCutoff ((d.N : ℝ)*M) d.W ≤
      K*bootstrapScalar d.T d.N d.V*d.W.card*
        (((d.N : ℝ)*M)^2+(d.N : ℝ)*localDiameter d.W)) :
    (d.W.card : ℝ) ≤ (comparisonConstant w+K)*bootstrapScalar d.T d.N d.V*(d.N : ℝ)*M +
      K*(bootstrapScalar d.T d.N d.V)^3*(d.N : ℝ)*localDiameter d.W/M := by
  let b := bootstrapScalar d.T d.N d.V
  let r : ℝ := d.W.card
  let C := comparisonConstant w
  have hb : 0 < b := d.scalar_pos hW
  have hr : 0 < r := by dsimp [r]; exact_mod_cast Finset.card_pos.mpr hW
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hdiag := completePairEnergy_diagonal_lower M d.W
  have hcomp := (uniform_comparison w).choose_spec.2 d.T d.V d.N M d.a d.W
    d.N_pos hM hscale d.V_pos d.separated d.coefficients d.large
  have hQ' := mul_le_mul_of_nonneg_left hQ (sq_nonneg b)
  have hraw : r ≤ C*b*(d.N : ℝ)*M+K*b^3*(d.N : ℝ)^2*M+
      K*b^3*(d.N : ℝ)*localDiameter d.W/M := by
    apply (mul_le_mul_iff_of_pos_right (mul_pos hMr hr)).1
    have he : (C*b*(d.N : ℝ)*M+K*b^3*(d.N : ℝ)^2*M+
        K*b^3*(d.N : ℝ)*localDiameter d.W/M)*((M : ℝ)*r) =
        C*b*(d.N : ℝ)*(M : ℝ)^2*r+K*b^3*r*(((d.N : ℝ)*M)^2+(d.N : ℝ)*localDiameter d.W) := by
      field_simp
      ring
    rw [he]
    dsimp [C, b, r, comparisonConstant] at *
    nlinarith
  have hs := mul_le_mul_of_nonneg_left hsmall
    (show 0 ≤ K*b*(d.N : ℝ)*M by positivity)
  dsimp [C, b, r] at *
  nlinarith

/-- Integer rounding of the optimal scale is permitted because comparison holds for every M>0. -/
theorem optimal_integer_scale {κ : ℝ} (d : LargeValueData κ) (hW : d.W.Nonempty)
    (hsmall : (d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2 ≤ 1) :
    ∃ M : ℕ, 0 < M ∧ (d.N : ℝ) ≤ (d.N : ℝ)*M ∧ (d.N : ℝ)*M ≤ 8*(d.T+1) ∧
      bootstrapScalar d.T d.N d.V*(d.N : ℝ)*M ≤
        (d.N : ℝ)*bootstrapScalar d.T d.N d.V+(d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2*Real.sqrt d.T ∧
      (bootstrapScalar d.T d.N d.V)^3*(d.N : ℝ)*localDiameter d.W/M ≤
        2*(d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2*Real.sqrt d.T := by
  let b := bootstrapScalar d.T d.N d.V
  let s := Real.sqrt d.T
  let M := ⌈b*s⌉₊
  have hb : 0 < b := d.scalar_pos hW
  have hT : 0 < d.T := by linarith [d.T_ge_two]
  have hs : 0 < s := Real.sqrt_pos.2 hT
  have hs2 : s^2 = d.T := Real.sq_sqrt hT.le
  have hNp : (0 : ℝ) < d.N := by exact_mod_cast d.N_pos
  have hM : 0 < M := (Nat.one_le_ceil_iff).2 (mul_pos hb hs)
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlo : b*s ≤ M := Nat.le_ceil _
  have hhi : (M : ℝ) ≤ b*s+1 := (Nat.ceil_lt_add_one (show 0 ≤ b*s by positivity)).le
  have hbalance : (d.N : ℝ)*b*s ≤ d.T := by
    have hi := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (d.N : ℝ)*d.T by positivity)
    have hnT := mul_le_mul_of_nonneg_right d.scale_upper hT.le
    have he : ((d.N : ℝ)*b*s)^2 = (d.N : ℝ)^2*b^2*d.T := by rw [mul_pow, mul_pow, hs2]
    have hz : 0 ≤ (d.N : ℝ)*b*s := by positivity
    dsimp [b] at hi he hz ⊢
    nlinarith
  refine ⟨M, hM, by nlinarith, ?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hhi hNp.le
    nlinarith [d.scale_upper, d.T_ge_two]
  · have hh := mul_le_mul_of_nonneg_left hhi (show 0 ≤ b*(d.N : ℝ) by positivity)
    dsimp [b, s] at hh
    nlinarith
  · have hd : localDiameter d.W ≤ 2*d.T := ((d.local_card_le (Finset.Subset.refl _)).2).trans
      (by linarith [d.T_ge_two])
    have hi := mul_le_mul_of_nonneg_left hd (show 0 ≤ b^3*(d.N : ℝ) by positivity)
    have hh := mul_le_mul_of_nonneg_left hlo (show 0 ≤ 2*(d.N : ℝ)*b^2*s by positivity)
    apply (div_le_iff₀ hMr).2
    change b^3*(d.N : ℝ)*localDiameter d.W ≤ 2*(d.N : ℝ)*b^2*s*M
    have he : 2*(d.N : ℝ)*b^2*s*(b*s) = 2*b^3*(d.N : ℝ)*d.T := by
      calc
        _ = 2*b^3*(d.N : ℝ)*s^2 := by ring
        _ = _ := by rw [hs2]
    rw [he] at hh
    nlinarith

/-- The proved kernel and rounding yield the two explicit Delta terms above a uniform threshold. -/
theorem large_values_with_divisors {κ : ℝ} (hκ : 0 < κ) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧ ∀ d : LargeValueData κ, T₀ ≤ d.T →
      (d.W.card : ℝ) ≤ C*((divisorMaximum d.T : ℝ)*(d.N : ℝ)^2/d.V^2 +
        (divisorMaximum d.T : ℝ)^2*(d.N : ℝ)^3*Real.sqrt d.T/d.V^4) := by
  let w := comparisonCutoff
  obtain ⟨K, T₀, hK, hT₀, hk⟩ := uniform_absorbed_kernel w hκ
  let C₀ := comparisonConstant w
  have hC₀ : 0 ≤ C₀ := comparisonConstant_nonneg w
  refine ⟨C₀+3*K+1, T₀, by positivity, hT₀, ?_⟩
  intro d hT
  by_cases hW : d.W.Nonempty
  · obtain ⟨hsmall, hkernel⟩ := hk d hW hT
    obtain ⟨M, hM, hlo, hhi, hterm₁, hterm₂⟩ := optimal_integer_scale d hW hsmall
    have hcard := cardinality_at_length w d hW hK hM hhi hsmall
      (hkernel d.W ((d.N : ℝ)*M) (Finset.Subset.refl _) hlo hhi)
    have h₁ := mul_le_mul_of_nonneg_left hterm₁ (show 0 ≤ C₀+K by positivity)
    have h₂ := mul_le_mul_of_nonneg_left hterm₂ hK
    have hbn := bootstrapScalar_nonneg d.T d.V d.N
    have hA : 0 ≤ (d.N : ℝ)*bootstrapScalar d.T d.N d.V := by positivity
    have hB : 0 ≤ (d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2*Real.sqrt d.T := by positivity
    have hform : (d.W.card : ℝ) ≤ (C₀+3*K+1)*
        ((d.N : ℝ)*bootstrapScalar d.T d.N d.V+
          (d.N : ℝ)*(bootstrapScalar d.T d.N d.V)^2*Real.sqrt d.T) := by
      dsimp [C₀] at *
      simp only [div_eq_mul_inv] at hcard h₂
      nlinarith [mul_nonneg hK hA]
    convert hform using 1
    unfold bootstrapScalar
    ring
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hW
    rw [hz, Finset.card_empty, Nat.cast_zero]
    positivity

end MathCollab.Density
