module
public import MathCollab.Density.ProductGrouping
public import MathCollab.Density.Packing

@[expose] public section

open Real Complex Set
open scoped BigOperators ComplexConjugate

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- The Gram identity is over all ordered pairs, with no time-pair restriction. -/
theorem completePairEnergy_gram (M : ℕ) (U : Finset ℝ) :
    completePairEnergy M U =
      ∑ q ∈ Finset.Ico M (2*M), ∑ r ∈ Finset.Ico M (2*M),
        ‖∑ t ∈ U, dirichletPhase ((q : ℝ)/M) t *
          conj (dirichletPhase ((r : ℝ)/M) t)‖^2 := by
  apply Complex.ofReal_injective
  have hh := complete_pair_expansion (Finset.Ico M (2*M)) U
    (fun q t => dirichletPhase ((q : ℝ)/M) t) (fun _ => 1)
  simpa only [one_mul, map_one, mul_one, ← dirichletPhase_sub,
    completePairEnergy, dyadicPolynomial, Complex.ofReal_sum] using hh

theorem completePairEnergy_diagonal_lower (M : ℕ) (U : Finset ℝ) :
    (M : ℝ)*(U.card : ℝ)^2 ≤ completePairEnergy M U := by
  rw [completePairEnergy_gram]
  calc
    _ = ∑ _q ∈ Finset.Ico M (2*M), (U.card : ℝ)^2 := by
      have hc : (Finset.Ico M (2*M)).card = M := by simp; omega
      simp only [Finset.sum_const, nsmul_eq_mul, hc]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro q hq
      have hd : ‖∑ t ∈ U, dirichletPhase ((q : ℝ)/M) t *
          conj (dirichletPhase ((q : ℝ)/M) t)‖^2 = (U.card : ℝ)^2 := by
        simp only [Complex.mul_conj', norm_dirichletPhase]
        simp
      rw [← hd]
      exact Finset.single_le_sum
        (f := fun r : ℕ => ‖∑ t ∈ U, dirichletPhase ((q : ℝ)/M) t *
          conj (dirichletPhase ((r : ℝ)/M) t)‖^2) (fun _ _ => sq_nonneg _) hq

theorem norm_sum_mul_sq_le {ι : Type*} (S : Finset ι) (a f : ι → ℂ)
    (ha : ∀ n ∈ S, ‖a n‖ ≤ 1) :
    ‖∑ n ∈ S, a n*f n‖^2 ≤ (S.card : ℝ)*∑ n ∈ S, ‖f n‖^2 := by
  have hnorm : ‖∑ n ∈ S, a n*f n‖ ≤ ∑ n ∈ S, ‖f n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (ha n hn) (norm_nonneg (f n))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun n => ‖f n‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hcs

/-- Insert D only where it is nonzero, then apply Cauchy--Schwarz in its N coefficients. -/
theorem detecting_insertion_bound {N : ℕ} {a : ℕ → ℂ} (U : Finset ℝ)
    (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ 1)
    (hD : ∀ t ∈ U, detectingPolynomial N a t ≠ 0) (g : ℝ → ℂ) :
    ‖∑ t ∈ U, g t‖^2 ≤ (N : ℝ)*
      ∑ n ∈ Finset.Ioc N (2*N),
        ‖∑ t ∈ U, dirichletPhase ((n : ℝ)/N) t * g t / detectingPolynomial N a t‖^2 := by
  have he : (∑ t ∈ U, g t) = ∑ n ∈ Finset.Ioc N (2*N),
      a n * ∑ t ∈ U, dirichletPhase ((n : ℝ)/N) t * g t / detectingPolynomial N a t := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    calc
      g t = detectingPolynomial N a t * g t / detectingPolynomial N a t := by
        field_simp [hD t ht]
      _ = _ := by
        simp only [detectingPolynomial, Finset.sum_mul, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro n hn
        ring
  rw [he]
  have hh := norm_sum_mul_sq_le (Finset.Ioc N (2*N)) a
    (fun n => ∑ t ∈ U, dirichletPhase ((n : ℝ)/N) t * g t / detectingPolynomial N a t) ha
  have hc : (Finset.Ioc N (2*N)).card = N := by simp; omega
  simpa only [hc] using hh

theorem normalized_product_phase {N M n q : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hn : 0 < n) (hq : 0 < q) (t : ℝ) :
    dirichletPhase ((n : ℝ)/N) t * dirichletPhase ((q : ℝ)/M) t =
      dirichletPhase (((n*q : ℕ) : ℝ)/((N : ℝ)*M)) t := by
  rw [← dirichletPhase_mul (by positivity) (by positivity)]
  congr 1
  push_cast
  ring

end MathCollab.Density
