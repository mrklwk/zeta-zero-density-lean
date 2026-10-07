module
public import MathCollab.Density.ComparisonExpansion

@[expose] public section

open Real Complex Set
open scoped BigOperators ComplexConjugate

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- The detecting polynomial, original product grouping, and nonnegative extension. -/
theorem comparison_extension_bound (w : ComparisonCutoff) {T : ℝ} {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hscale : (N : ℝ)*M ≤ 8*(T+1))
    (a : ℕ → ℂ) (U : Finset ℝ)
    (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ 1)
    (hD : ∀ t ∈ U, detectingPolynomial N a t ≠ 0) :
    completePairEnergy M U ≤ (N : ℝ)*(divisorMaximum T : ℝ)*comparisonExtension w N M a U := by
  let Q := Finset.Ico M (2*M)
  let F := fun r m : ℕ => ‖∑ t ∈ U, dirichletPhase (m/((N : ℝ)*M)) t *
    conj (dirichletPhase ((r : ℝ)/M) t) / detectingPolynomial N a t‖^2
  rw [completePairEnergy_gram, Finset.sum_comm]
  calc
    _ ≤ ∑ r ∈ Q, (N : ℝ)*∑ n ∈ Finset.Ioc N (2*N), ∑ q ∈ Q, F r (n*q) := by
      apply Finset.sum_le_sum
      intro r hr
      calc
        _ ≤ ∑ q ∈ Q, (N : ℝ)*∑ n ∈ Finset.Ioc N (2*N), F r (n*q) := by
          apply Finset.sum_le_sum
          intro q hq
          have hh := detecting_insertion_bound U ha hD
            (fun t => dirichletPhase ((q : ℝ)/M) t * conj (dirichletPhase ((r : ℝ)/M) t))
          have hqp : 0 < q := hM.trans_le (Finset.mem_Ico.mp hq).1
          have he : (∑ n ∈ Finset.Ioc N (2*N),
              ‖∑ t ∈ U, dirichletPhase ((n : ℝ)/N) t *
                (dirichletPhase ((q : ℝ)/M) t * conj (dirichletPhase ((r : ℝ)/M) t)) /
                  detectingPolynomial N a t‖^2) = ∑ n ∈ Finset.Ioc N (2*N), F r (n*q) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnp : 0 < n := hN.trans (Finset.mem_Ioc.mp hn).1
            simp only [← mul_assoc, normalized_product_phase hN hM hnp hqp, F, Nat.cast_mul]
          rwa [he] at hh
        _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ∑ r ∈ Q, (N : ℝ)*((divisorMaximum T : ℝ)*
        ∑ m ∈ Finset.range (⌈5*((N : ℝ)*M)⌉₊+1), w (m/((N : ℝ)*M))*F r m) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (product_grouping_cutoff w hN hM hscale (F r)
        (fun _ => sq_nonneg _)) (Nat.cast_nonneg N)
    _ = _ := by simp only [comparisonExtension, Q, F, ← Finset.mul_sum, mul_assoc]

theorem dyadicPolynomial_norm_le (M : ℕ) (v : ℝ) : ‖dyadicPolynomial M v‖ ≤ M := by
  have hc : (Finset.Ico M (2*M)).card = M := by simp; omega
  calc
    _ ≤ ∑ q ∈ Finset.Ico M (2*M), ‖dirichletPhase ((q : ℝ)/M) v‖ := norm_sum_le _ _
    _ = _ := by simp only [norm_dirichletPhase, Finset.sum_const, nsmul_eq_mul, mul_one, hc]

theorem detecting_pair_division_bound {T V : ℝ} {N : ℕ} {a : ℕ → ℂ}
    (hV : 0 < V) {t u : ℝ} (ht : V ≤ ‖detectingPolynomial N a t‖)
    (hu : V ≤ ‖detectingPolynomial N a u‖) (z : ℂ) :
    (N : ℝ)*(divisorMaximum T : ℝ)*
        ‖z/(detectingPolynomial N a t * conj (detectingPolynomial N a u))‖ ≤
      bootstrapScalar T N V * ‖z‖ := by
  have hden : V^2 ≤ ‖detectingPolynomial N a t‖*‖detectingPolynomial N a u‖ := by
    nlinarith [mul_le_mul ht hu hV.le (norm_nonneg (detectingPolynomial N a t))]
  rw [norm_div, norm_mul, Complex.norm_conj]
  calc
    _ ≤ (N : ℝ)*(divisorMaximum T : ℝ)*(‖z‖/V^2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hden
    _ = _ := by dsimp [bootstrapScalar]; ring

theorem bootstrapScalar_nonneg (T V : ℝ) (N : ℕ) : 0 ≤ bootstrapScalar T N V := by
  unfold bootstrapScalar
  positivity

/-- Continuous-term control uses one absolute row-sum constant, independent of |U|. -/
theorem comparison_continuous_bound (w : ComparisonCutoff) {C T V : ℝ} {N M : ℕ}
    (hC : 0 ≤ C) (hdecay : ∀ v : ℝ, ‖cutoffIntegral w.toReflectionCutoff v‖ ≤ C/(1+|v|)^2)
    (hV : 0 < V) (a : ℕ → ℂ) (U : Finset ℝ) (hsep : oneSeparated U)
    (hlarge : ∀ t ∈ U, V ≤ ‖detectingPolynomial N a t‖) :
    (N : ℝ)*(divisorMaximum T : ℝ)*
      (∑ t ∈ U, ∑ u ∈ U,
        ‖(((N : ℝ)*M : ℝ) : ℂ)*cutoffIntegral w.toReflectionCutoff (t-u) *
          conj (dyadicPolynomial M (t-u)) /
          (detectingPolynomial N a t * conj (detectingPolynomial N a u))‖) ≤
      (C*separationMass)*bootstrapScalar T N V*(N : ℝ)*(M : ℝ)^2*U.card := by
  let b := bootstrapScalar T N V
  have hb : 0 ≤ b := bootstrapScalar_nonneg T V N
  have hp (t u : ℝ) (ht : t ∈ U) (hu : u ∈ U) :
      (N : ℝ)*(divisorMaximum T : ℝ)*
        ‖(((N : ℝ)*M : ℝ) : ℂ)*cutoffIntegral w.toReflectionCutoff (t-u) *
          conj (dyadicPolynomial M (t-u)) /
          (detectingPolynomial N a t * conj (detectingPolynomial N a u))‖ ≤
      b*(N : ℝ)*(M : ℝ)^2*C*(1/(1+|t-u|)^2) := by
    calc
      _ ≤ b*‖(((N : ℝ)*M : ℝ) : ℂ)*cutoffIntegral w.toReflectionCutoff (t-u) *
          conj (dyadicPolynomial M (t-u))‖ :=
        detecting_pair_division_bound hV (hlarge t ht) (hlarge u hu) _
      _ = b*((N : ℝ)*M)*‖cutoffIntegral w.toReflectionCutoff (t-u)‖*
          ‖dyadicPolynomial M (t-u)‖ := by
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)*M)]
        ring
      _ ≤ b*((N : ℝ)*M)*(C/(1+|t-u|)^2)*(M : ℝ) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (hdecay (t-u)) (by positivity)
        · exact dyadicPolynomial_norm_le M (t-u)
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  calc
    _ = ∑ t ∈ U, ∑ u ∈ U,
        (N : ℝ)*(divisorMaximum T : ℝ)*
          ‖(((N : ℝ)*M : ℝ) : ℂ)*cutoffIntegral w.toReflectionCutoff (t-u) *
            conj (dyadicPolynomial M (t-u)) /
            (detectingPolynomial N a t * conj (detectingPolynomial N a u))‖ := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ t ∈ U, ∑ u ∈ U, b*(N : ℝ)*(M : ℝ)^2*C*(1/(1+|t-u|)^2) :=
      Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun u hu => hp t u ht hu))
    _ = (b*(N : ℝ)*(M : ℝ)^2*C)*(∑ t ∈ U, ∑ u ∈ U, 1/(1+|t-u|)^2) := by
      simp only [Finset.mul_sum]
    _ ≤ (b*(N : ℝ)*(M : ℝ)^2*C)*(separationMass*U.card) :=
      mul_le_mul_of_nonneg_left (separated_decay_pairs hsep) (by positivity)
    _ = _ := by dsimp [b]; ring

theorem comparison_remainder_bound (w : ComparisonCutoff) {T V : ℝ} {N M : ℕ}
    (hV : 0 < V) (a : ℕ → ℂ) (U : Finset ℝ)
    (hlarge : ∀ t ∈ U, V ≤ ‖detectingPolynomial N a t‖) :
    (N : ℝ)*(divisorMaximum T : ℝ)*
      (∑ t ∈ U, ∑ u ∈ U,
        ‖hKernel w.toReflectionCutoff ((N : ℝ)*M) (t-u) *
          conj (dyadicPolynomial M (t-u)) /
          (detectingPolynomial N a t * conj (detectingPolynomial N a u))‖) ≤
      (bootstrapScalar T N V)^2/2 * kernelEnergy w.toReflectionCutoff ((N : ℝ)*M) U +
        completePairEnergy M U / 2 := by
  let b := bootstrapScalar T N V
  have hp (t u : ℝ) (ht : t ∈ U) (hu : u ∈ U) :
      (N : ℝ)*(divisorMaximum T : ℝ)*
        ‖hKernel w.toReflectionCutoff ((N : ℝ)*M) (t-u) *
          conj (dyadicPolynomial M (t-u)) /
          (detectingPolynomial N a t * conj (detectingPolynomial N a u))‖ ≤
      b^2/2*‖hKernel w.toReflectionCutoff ((N : ℝ)*M) (t-u)‖^2 +
        ‖dyadicPolynomial M (t-u)‖^2/2 := by
    calc
      _ ≤ b*‖hKernel w.toReflectionCutoff ((N : ℝ)*M) (t-u) *
          conj (dyadicPolynomial M (t-u))‖ :=
        detecting_pair_division_bound hV (hlarge t ht) (hlarge u hu) _
      _ = b*‖hKernel w.toReflectionCutoff ((N : ℝ)*M) (t-u)‖*
          ‖dyadicPolynomial M (t-u)‖ := by rw [norm_mul, Complex.norm_conj]; ring
      _ ≤ _ := by nlinarith [sq_nonneg (b*‖hKernel w.toReflectionCutoff ((N : ℝ)*M) (t-u)‖ - ‖dyadicPolynomial M (t-u)‖)]
  calc
    _ = ∑ t ∈ U, ∑ u ∈ U,
        (N : ℝ)*(divisorMaximum T : ℝ)*
          ‖hKernel w.toReflectionCutoff ((N : ℝ)*M) (t-u) *
            conj (dyadicPolynomial M (t-u)) /
            (detectingPolynomial N a t * conj (detectingPolynomial N a u))‖ := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ t ∈ U, ∑ u ∈ U,
        (b^2/2*‖hKernel w.toReflectionCutoff ((N : ℝ)*M) (t-u)‖^2 +
          ‖dyadicPolynomial M (t-u)‖^2/2) :=
      Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun u hu => hp t u ht hu))
    _ = _ := by
      simp only [b, kernelEnergy, completePairEnergy, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.sum_div]

/-- The comparison constant is selected solely from w, before every original data parameter. -/
theorem uniform_comparison (w : ComparisonCutoff) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T V : ℝ) (N M : ℕ) (a : ℕ → ℂ) (U : Finset ℝ),
      0 < N → 0 < M → (N : ℝ)*M ≤ 8*(T+1) → 0 < V → oneSeparated U →
      (∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ 1) →
      (∀ t ∈ U, V ≤ ‖detectingPolynomial N a t‖) →
      completePairEnergy M U ≤ C*bootstrapScalar T N V*(N : ℝ)*(M : ℝ)^2*U.card +
        (bootstrapScalar T N V)^2*kernelEnergy w.toReflectionCutoff ((N : ℝ)*M) U := by
  obtain ⟨C₀, hC₀, hdecay⟩ := cutoffIntegral_quadratic_decay w.toReflectionCutoff
  refine ⟨2*C₀*separationMass, mul_nonneg (by positivity) separationMass_nonneg, ?_⟩
  intro T V N M a U hN hM hscale hV hsep ha hlarge
  have hD : ∀ t ∈ U, detectingPolynomial N a t ≠ 0 := by
    intro t ht he
    have hh := hlarge t ht
    rw [he, norm_zero] at hh
    linarith
  have hext := comparison_extension_bound w hN hM hscale a U ha hD
  have hC := comparison_continuous_bound w hC₀ hdecay hV a U hsep hlarge (T := T) (M := M)
  have hR := comparison_remainder_bound w hV a U hlarge (T := T) (M := M)
  have hnorm : comparisonExtension w N M a U = ‖(comparisonExtension w N M a U : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (comparisonExtension_nonneg w N M a U)]
  rw [hnorm, comparisonExtension_identity w hN hM] at hext
  have htri := (norm_sum_le U (fun t => ∑ u ∈ U,
    ((((N : ℝ)*M : ℝ) : ℂ)*cutoffIntegral w.toReflectionCutoff (t-u) *
      conj (dyadicPolynomial M (t-u)) /
      (detectingPolynomial N a t * conj (detectingPolynomial N a u)) +
    hKernel w.toReflectionCutoff ((N : ℝ)*M) (t-u) * conj (dyadicPolynomial M (t-u)) /
      (detectingPolynomial N a t * conj (detectingPolynomial N a u))))).trans
      (Finset.sum_le_sum (fun t _ => (norm_sum_le U _).trans
        (Finset.sum_le_sum (fun u _ => norm_add_le _ _))))
  have hh := mul_le_mul_of_nonneg_left htri
    (show 0 ≤ (N : ℝ)*(divisorMaximum T : ℝ) by positivity)
  simp only [Finset.sum_add_distrib, mul_add] at hh hext
  nlinarith

end MathCollab.Density
