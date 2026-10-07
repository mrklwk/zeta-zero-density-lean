module
public import MathCollab.Density.ReflectionDefinitions

@[expose] public section

open Complex
open scoped BigOperators ComplexConjugate

noncomputable section
namespace MathCollab.Density

/-- Expansion of the complete time-pair square into a nonnegative mode-pair Gram matrix. -/
theorem complete_pair_expansion {ι κ : Type*} (Q : Finset ι) (U : Finset κ)
    (a : ι → κ → ℂ) (c : ι → ℂ) :
    ((∑ t ∈ U, ∑ u ∈ U,
      ‖∑ q ∈ Q, c q * (a q t * conj (a q u))‖ ^ 2 : ℝ) : ℂ) =
    ∑ q ∈ Q, ∑ r ∈ Q, c q * conj (c r) *
      ((‖∑ t ∈ U, a q t * conj (a r t)‖ ^ 2 : ℝ) : ℂ) := by
  have hn (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [Complex.ofReal_sum, hn, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := U) (t := Q)]
  rw [Finset.sum_comm (s := Q) (t := Q)]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  simp only [conj_conj]
  ring

/-- Coefficient domination requires all pairs from the same finite set. -/
theorem complete_pair_coefficient_domination {ι κ : Type*} (Q : Finset ι) (U : Finset κ)
    (a : ι → κ → ℂ) (c : ι → ℂ) (hc : ∀ q ∈ Q, ‖c q‖ ≤ 1) :
    (∑ t ∈ U, ∑ u ∈ U, ‖∑ q ∈ Q, c q * (a q t * conj (a q u))‖ ^ 2) ≤
      ∑ t ∈ U, ∑ u ∈ U, ‖∑ q ∈ Q, a q t * conj (a q u)‖ ^ 2 := by
  let E := ∑ t ∈ U, ∑ u ∈ U, ‖∑ q ∈ Q, c q * (a q t * conj (a q u))‖ ^ 2
  let S := ∑ t ∈ U, ∑ u ∈ U, ‖∑ q ∈ Q, a q t * conj (a q u)‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun u _ => sq_nonneg _
  have hS : 0 ≤ S := Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun u _ => sq_nonneg _
  have hEexp := complete_pair_expansion Q U a c
  have hSexp := complete_pair_expansion Q U a (fun _ => 1)
  simp only [one_mul, map_one, mul_one] at hSexp
  have hreal : S = ∑ q ∈ Q, ∑ r ∈ Q, ‖∑ t ∈ U, a q t * conj (a r t)‖ ^ 2 := by
    apply Complex.ofReal_injective
    simpa only [S, Complex.ofReal_sum] using hSexp
  change E ≤ S
  calc
    E = ‖(E : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hE]
    _ = ‖∑ q ∈ Q, ∑ r ∈ Q, c q * conj (c r) *
        ((‖∑ t ∈ U, a q t * conj (a r t)‖ ^ 2 : ℝ) : ℂ)‖ := by rw [hEexp]
    _ ≤ ∑ q ∈ Q, ∑ r ∈ Q, ‖c q * conj (c r) *
        ((‖∑ t ∈ U, a q t * conj (a r t)‖ ^ 2 : ℝ) : ℂ)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => norm_sum_le _ _)
    _ ≤ ∑ q ∈ Q, ∑ r ∈ Q, ‖∑ t ∈ U, a q t * conj (a r t)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hh : ‖c q‖ * ‖c r‖ ≤ 1 := by
        simpa using mul_le_mul (hc q hq) (hc r hr) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (one_mul _)
    _ = S := hreal.symm

theorem dirichletPhase_sub (x t u : ℝ) :
    dirichletPhase x (t-u) = dirichletPhase x t * conj (dirichletPhase x u) := by
  unfold dirichletPhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The coefficient-domination statement for the source's P_M and S_M. -/
theorem completePairEnergy_coefficient_domination (M : ℕ) (U : Finset ℝ)
    (c : ℕ → ℂ) (hc : ∀ q ∈ Finset.Ico M (2*M), ‖c q‖ ≤ 1) :
    (∑ t ∈ U, ∑ u ∈ U, ‖∑ q ∈ Finset.Ico M (2*M),
      c q * dirichletPhase ((q : ℝ) / M) (t-u)‖ ^ 2) ≤ completePairEnergy M U := by
  have hh := complete_pair_coefficient_domination (Finset.Ico M (2*M)) U
    (fun q t => dirichletPhase ((q : ℝ) / M) t) c hc
  simpa only [← dirichletPhase_sub, completePairEnergy, dyadicPolynomial] using hh

end MathCollab.Density
