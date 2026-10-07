module
public import MathCollab.Density.LargeValuesOptimization

@[expose] public section

open Real Complex Set
open scoped BigOperators

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The fixed packet target, with the epsilon constant chosen before every configuration. -/
theorem large_values_data {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : LargeValueData κ,
      (d.W.card : ℝ) ≤ C*d.T^ε*((d.N : ℝ)^2/d.V^2+
        (d.N : ℝ)^3*Real.sqrt d.T/d.V^4) := by
  obtain ⟨A, T₀, hA, hT₀, hlarge⟩ := large_values_with_divisors hκ
  obtain ⟨D, hD, hdiv⟩ := divisorMaximum_subpower (show 0 < ε/2 by positivity)
  let C := A*D^2+T₀+1
  have hDp : 0 < D := by linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro d
  have hT : 0 < d.T := by linarith [d.T_ge_two]
  have hT1 : 1 ≤ d.T := by linarith [d.T_ge_two]
  have hV := d.V_pos
  have hpow1 : 1 ≤ d.T^ε := Real.one_le_rpow hT1 hε.le
  have hF : 0 ≤ (d.N : ℝ)^2/d.V^2+(d.N : ℝ)^3*Real.sqrt d.T/d.V^4 := by positivity
  by_cases hW : d.W.Nonempty
  · by_cases hbig : T₀ ≤ d.T
    · have hdelta := hdiv d.T d.T_ge_two
      have hdelta₂ : (divisorMaximum d.T : ℝ)^2 ≤ D^2*d.T^ε := by
        have hh := pow_le_pow_left₀ (Nat.cast_nonneg _) hdelta 2
        have he : (D*d.T^(ε/2))^2 = D^2*d.T^ε := by
          rw [mul_pow, ← Real.rpow_natCast (d.T^(ε/2)) 2, ← Real.rpow_mul hT.le]
          congr 1
          congr 1
          ring
        exact hh.trans_eq he
      have hdelta₁ : (divisorMaximum d.T : ℝ) ≤ D^2*d.T^ε := by
        have hh : (d.T : ℝ)^(ε/2) ≤ d.T^ε :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
        have hi := mul_le_mul_of_nonneg_left hh hDp.le
        have hj := mul_le_mul_of_nonneg_right (show D ≤ D^2 by nlinarith) (Real.rpow_nonneg hT.le ε)
        exact hdelta.trans (hi.trans hj)
      have h₁ := mul_le_mul_of_nonneg_right hdelta₁ (show 0 ≤ (d.N : ℝ)^2/d.V^2 by positivity)
      have h₂ := mul_le_mul_of_nonneg_right hdelta₂
        (show 0 ≤ (d.N : ℝ)^3*Real.sqrt d.T/d.V^4 by positivity)
      have hraw : (divisorMaximum d.T : ℝ)*(d.N : ℝ)^2/d.V^2 +
          (divisorMaximum d.T : ℝ)^2*(d.N : ℝ)^3*Real.sqrt d.T/d.V^4 ≤
            D^2*d.T^ε*((d.N : ℝ)^2/d.V^2+(d.N : ℝ)^3*Real.sqrt d.T/d.V^4) := by
        simp only [div_eq_mul_inv] at h₁ h₂ ⊢
        nlinarith
      have hh := (hlarge d hbig).trans (mul_le_mul_of_nonneg_left hraw hA.le)
      have hcoef : A*D^2 ≤ C := by dsimp [C]; linarith
      have hi := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (Real.rpow_nonneg hT.le ε) hF)
      nlinarith
    · have hvn := d.height_le_length hW
      have hN : (0 : ℝ) < d.N := by exact_mod_cast d.N_pos
      have hF1 : 1 ≤ (d.N : ℝ)^2/d.V^2+(d.N : ℝ)^3*Real.sqrt d.T/d.V^4 := by
        have hh : (1 : ℝ) ≤ (d.N : ℝ)^2/d.V^2 := (le_div_iff₀ (by positivity)).2 (by nlinarith)
        have hi : 0 ≤ (d.N : ℝ)^3*Real.sqrt d.T/d.V^4 := by positivity
        linarith
      have hr := (d.local_card_le (Finset.Subset.refl d.W)).1.trans (d.local_card_le (Finset.Subset.refl d.W)).2
      have hc0 : T₀+1 ≤ C := by dsimp [C]; nlinarith [sq_nonneg D]
      have hprod : 1 ≤ d.T^ε*((d.N : ℝ)^2/d.V^2+(d.N : ℝ)^3*Real.sqrt d.T/d.V^4) := by nlinarith
      have hh := mul_le_mul_of_nonneg_left hprod hC.le
      calc
        _ ≤ d.T+1 := hr
        _ ≤ T₀+1 := by linarith
        _ ≤ C := hc0
        _ ≤ _ := by nlinarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hW, Finset.card_empty, Nat.cast_zero]
    positivity

/-- Draft Theorem 1.3 with all original hypotheses exposed and no cutoff or smallness premise. -/
theorem large_values {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T V : ℝ) (N : ℕ) (a : ℕ → ℂ) (W : Finset ℝ),
      2 ≤ T → 0 < N → 0 < V → T^(1/3 : ℝ) ≤ (N : ℝ) → (N : ℝ) ≤ T →
      (N : ℝ)^(3/4+κ) ≤ V →
      (∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ 1) →
      (∃ t₀ : ℝ, ∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T) →
      (∀ t ∈ W, ∀ u ∈ W, t ≠ u → 1 ≤ |t-u|) →
      (∀ t ∈ W, V ≤ ‖detectingPolynomial N a t‖) →
      (W.card : ℝ) ≤ C*T^ε*((N : ℝ)^2/V^2+(N : ℝ)^3*Real.sqrt T/V^4) := by
  obtain ⟨C, hC, hbound⟩ := large_values_data hκ hε
  refine ⟨C, hC, ?_⟩
  intro T V N a W hT hN hV hlow hhigh hheight ha hloc hsep hlarge
  obtain ⟨t₀, ht₀⟩ := hloc
  exact hbound
    { T := T, N := N, V := V, a := a, W := W, t₀ := t₀
      T_ge_two := hT, N_pos := hN, V_pos := hV, scale_lower := hlow, scale_upper := hhigh
      height := hheight, coefficients := ha, location := ht₀, separated := hsep, large := hlarge }

end MathCollab.Density
