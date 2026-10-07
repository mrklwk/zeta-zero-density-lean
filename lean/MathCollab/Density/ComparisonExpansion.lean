module
public import MathCollab.Density.ComparisonAlgebra

@[expose] public section

open Real Complex Set
open scoped BigOperators ComplexConjugate

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

theorem weighted_mode_expansion {ι κ τ : Type*} (Q : Finset ι) (R : Finset κ) (U : Finset τ)
    (w : κ → ℝ) (f : κ → τ → ℂ) (g : ι → τ → ℂ) (D : τ → ℂ) :
    ((∑ q ∈ Q, ∑ m ∈ R, w m * ‖∑ t ∈ U, f m t * conj (g q t) / D t‖^2 : ℝ) : ℂ) =
      ∑ t ∈ U, ∑ u ∈ U,
        (∑ m ∈ R, (w m : ℂ) * (f m t * conj (f m u))) *
          (∑ q ∈ Q, conj (g q t) * g q u) / (D t * conj (D u)) := by
  have hn (z : ℂ) : ((‖z‖^2 : ℝ) : ℂ) = z*conj z := by
    rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, hn, map_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  simp_rw [Finset.sum_comm (s := R) (t := U)]
  simp_rw [Finset.sum_comm (s := Q) (t := U)]
  simp_rw [Finset.sum_comm (s := Q) (t := R)]
  conv_lhs => rw [Finset.sum_comm (s := U) (t := U)]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro q hq
  ring_nf
  simp only [map_mul, map_inv₀, conj_conj]
  ring

theorem cutoff_finite_sum (w : ReflectionCutoff) {L : ℝ} (hL : 0 < L) (v : ℝ) :
    (∑ n ∈ Finset.range (⌈5*L⌉₊+1), (w ((n : ℝ)/L) : ℂ)*dirichletPhase ((n : ℝ)/L) v) =
      (L : ℂ)*cutoffIntegral w v + hKernel w L v := by
  have he : (∑' n : ℕ, (w ((n : ℝ)/L) : ℂ)*dirichletPhase ((n : ℝ)/L) v) =
      ∑ n ∈ Finset.range (⌈5*L⌉₊+1), (w ((n : ℝ)/L) : ℂ)*dirichletPhase ((n : ℝ)/L) v := by
    apply tsum_eq_sum
    intro n hn
    have hn' : ⌈5*L⌉₊ < n := by simpa using hn
    have hbig : 5 < (n : ℝ)/L := (lt_div_iff₀ hL).2 (Nat.lt_of_ceil_lt hn')
    have hz : w ((n : ℝ)/L) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => (not_le.mpr hbig) (w.support h).2)
    simp only [hz, Complex.ofReal_zero, zero_mul]
  rw [hKernel, he]
  ring

def comparisonExtension (w : ComparisonCutoff) (N M : ℕ) (a : ℕ → ℂ) (U : Finset ℝ) : ℝ :=
  ∑ q ∈ Finset.Ico M (2*M), ∑ m ∈ Finset.range (⌈5*((N : ℝ)*M)⌉₊+1),
    w (m/((N : ℝ)*M)) *
      ‖∑ t ∈ U, dirichletPhase (m/((N : ℝ)*M)) t *
        conj (dirichletPhase ((q : ℝ)/M) t) / detectingPolynomial N a t‖^2

theorem comparisonExtension_nonneg (w : ComparisonCutoff) (N M : ℕ) (a : ℕ → ℂ) (U : Finset ℝ) :
    0 ≤ comparisonExtension w N M a U :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => mul_nonneg (w.nonneg _) (sq_nonneg _)))

theorem comparisonExtension_identity (w : ComparisonCutoff) {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (a : ℕ → ℂ) (U : Finset ℝ) :
    (comparisonExtension w N M a U : ℂ) =
      ∑ t ∈ U, ∑ u ∈ U,
        ((((N : ℝ)*M : ℝ) : ℂ)*cutoffIntegral w.toReflectionCutoff (t-u) *
          conj (dyadicPolynomial M (t-u)) /
          (detectingPolynomial N a t * conj (detectingPolynomial N a u)) +
        hKernel w.toReflectionCutoff ((N : ℝ)*M) (t-u) *
          conj (dyadicPolynomial M (t-u)) /
          (detectingPolynomial N a t * conj (detectingPolynomial N a u))) := by
  rw [comparisonExtension, weighted_mode_expansion]
  apply Finset.sum_congr rfl
  intro t ht
  apply Finset.sum_congr rfl
  intro u hu
  simp only [← dirichletPhase_sub]
  have hq : (∑ q ∈ Finset.Ico M (2*M), conj (dirichletPhase ((q : ℝ)/M) t) *
      dirichletPhase ((q : ℝ)/M) u) = conj (dyadicPolynomial M (t-u)) := by
    simp only [dyadicPolynomial, map_sum, dirichletPhase_sub, map_mul, conj_conj]
  rw [hq, cutoff_finite_sum w.toReflectionCutoff (by positivity)]
  ring

end MathCollab.Density
