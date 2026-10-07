module
public import MathCollab.Density.FiniteDetector

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The fixed coefficients in the packet's Taylor family. Neither coordinate
of a zero occurs in this definition. -/
def detectorTaylorCoefficient (T : ℝ) (N j n : ℕ) : ℂ :=
  firstDetectorCoefficient T n * (((2*(n : ℝ)/N-3 : ℝ) : ℂ)^j)

def detectorTaylorPolynomial (T : ℝ) (N j : ℕ) (t : ℝ) : ℂ :=
  detectingPolynomial N (detectorTaylorCoefficient T N j) (-t)

/-- The rising-factorial quotient, kept as a product of normalized factors. -/
def detectorTaylorRatio (β : ℝ) (j : ℕ) : ℝ :=
  ∏ l ∈ Finset.range j, (β+(l : ℝ))/(1+(l : ℝ))

def detectorTaylorWeight (β : ℝ) (j : ℕ) : ℝ :=
  detectorTaylorRatio β j * (-1/3 : ℝ)^j

theorem detectorTaylorRatio_bounds {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) (j : ℕ) :
    0 ≤ detectorTaylorRatio β j ∧ detectorTaylorRatio β j ≤ 1 := by
  have hn : ∀ l : ℕ, 0 ≤ (β+(l : ℝ))/(1+(l : ℝ)) := fun l => by positivity
  have hu : ∀ l : ℕ, (β+(l : ℝ))/(1+(l : ℝ)) ≤ 1 := fun l =>
    (div_le_one (by positivity)).2 (by linarith)
  exact ⟨Finset.prod_nonneg (fun l _ => hn l),
    Finset.prod_le_one₀ (fun l _ => hn l) (fun l _ => hu l)⟩

theorem abs_detectorTaylorWeight_le {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) (j : ℕ) :
    |detectorTaylorWeight β j| ≤ (1/3 : ℝ)^j := by
  have hr := detectorTaylorRatio_bounds hβ hβ' j
  rw [detectorTaylorWeight, abs_mul, abs_of_nonneg hr.1, abs_pow]
  norm_num
  exact hr.2

/-- The whole scalar-weight sum is bounded by 3/2, with no J loss. -/
theorem sum_abs_detectorTaylorWeight_le {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1) (J : ℕ) :
    ∑ j ∈ Finset.range J, |detectorTaylorWeight β j| ≤ 3/2 := by
  have hg := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/3) (by norm_num : (1/3 : ℝ) < 1)
  calc
    _ ≤ ∑ j ∈ Finset.range J, (1/3 : ℝ)^j := Finset.sum_le_sum (fun j _ => abs_detectorTaylorWeight_le hβ hβ' j)
    _ ≤ ∑' j : ℕ, (1/3 : ℝ)^j := hg.summable.sum_le_tsum _ (fun j _ => by positivity)
    _ = _ := by rw [hg.tsum_eq]; norm_num

theorem norm_detectorTaylorCoefficient_le {T : ℝ} {N n : ℕ}
    (hT : 0 < T) (hN : 0 < N) (hn : n ∈ Finset.Ioc N (2*N)) (j : ℕ) :
    ‖detectorTaylorCoefficient T N j n‖ ≤ (n.divisors.card : ℝ) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hlo : (N : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1.le
  have hhi : (n : ℝ) ≤ 2*N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hr : |2*(n : ℝ)/N-3| ≤ 1 := by
    apply abs_le.mpr
    have hl : (2 : ℝ) ≤ 2*(n : ℝ)/N := (le_div_iff₀ hNpos).2 (by linarith)
    have hh : 2*(n : ℝ)/N ≤ 4 := (div_le_iff₀ hNpos).2 (by linarith)
    constructor <;> linarith
  rw [detectorTaylorCoefficient, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hp : |2*(n : ℝ)/N-3|^j ≤ 1 := pow_le_one₀ (abs_nonneg _) hr
  exact (mul_le_mul (firstDetectorCoefficient_norm_le hT n) hp (by positivity) (by positivity)).trans_eq (mul_one _)

/-- Finite bounded-weight extraction. The bound costs an absolute factor 2,
never the number of Taylor terms. It does not assert the Taylor identity. -/
theorem exists_large_taylor_component {β : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (J : ℕ) (D : ℕ → ℂ) :
    ∃ j ∈ Finset.range (J+1),
      ‖∑ k ∈ Finset.range (J+1), (detectorTaylorWeight β k : ℂ)*D k‖/2 ≤ ‖D j‖ := by
  let S : ℂ := ∑ k ∈ Finset.range (J+1), (detectorTaylorWeight β k : ℂ)*D k
  by_contra h
  push Not at h
  have hb : ∀ k ∈ Finset.range (J+1), ‖D k‖ ≤ ‖S‖/2 := fun k hk => (h k hk).le
  have hp : 0 < ‖S‖ := by
    have h0 := h 0 (Finset.mem_range.mpr (by omega))
    change ‖D 0‖ < ‖S‖/2 at h0
    linarith [norm_nonneg (D 0)]
  have he : ‖S‖ ≤ (3/2)*(‖S‖/2) := by
    calc
      _ ≤ ∑ k ∈ Finset.range (J+1), ‖(detectorTaylorWeight β k : ℂ)*D k‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range (J+1), |detectorTaylorWeight β k| *‖D k‖ := by simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ∑ k ∈ Finset.range (J+1), |detectorTaylorWeight β k| *(‖S‖/2) := by gcongr with k hk; exact hb k hk
      _ = (∑ k ∈ Finset.range (J+1), |detectorTaylorWeight β k|)*(‖S‖/2) := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (sum_abs_detectorTaylorWeight_le hβ hβ' _) (by positivity)
  linarith

/-- Uniform in the Taylor index and ordinate, before any beta approximation. -/
theorem norm_detectorTaylorPolynomial_le {T : ℝ} {N : ℕ}
    (hT : 0 < T) (hN : 0 < N) (j : ℕ) (t : ℝ) :
    ‖detectorTaylorPolynomial T N j t‖ ≤ 2*(N : ℝ)^2 := by
  unfold detectorTaylorPolynomial detectingPolynomial
  calc
    _ ≤ ∑ n ∈ Finset.Ioc N (2*N), ‖detectorTaylorCoefficient T N j n * dirichletPhase ((n : ℝ)/N) (-t)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ioc N (2*N), (2*(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_dirichletPhase, mul_one]
      have hc : (n.divisors.card : ℝ) ≤ n := by exact_mod_cast Nat.card_divisors_le_self n
      have hn' : (n : ℝ) ≤ 2*N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
      exact (norm_detectorTaylorCoefficient_le hT hN hn j).trans (hc.trans hn')
    _ = _ := by
      simp only [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      rw [show 2*N-N = N by omega]
      ring

/-- The tail of the actual fixed polynomial family has geometric decay.
Identifying its full weighted series with the beta-dependent block is separate. -/
theorem norm_detectorTaylor_tail_le {T β : ℝ} {N : ℕ}
    (hT : 0 < T) (hN : 0 < N) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (J : ℕ) (t : ℝ) :
    ‖∑' j : ℕ, (detectorTaylorWeight β (j+J) : ℂ)*detectorTaylorPolynomial T N (j+J) t‖ ≤
      3*(N : ℝ)^2*(1/3 : ℝ)^J := by
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/3)
    (by norm_num : (1/3 : ℝ) < 1)).mul_left (2*(N : ℝ)^2*(1/3 : ℝ)^J)
  have hb : ∀ j : ℕ, ‖(detectorTaylorWeight β (j+J) : ℂ)*detectorTaylorPolynomial T N (j+J) t‖ ≤
      (2*(N : ℝ)^2*(1/3 : ℝ)^J)*(1/3 : ℝ)^j := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (1/3 : ℝ)^(j+J)*(2*(N : ℝ)^2) :=
        mul_le_mul (abs_detectorTaylorWeight_le hβ hβ' _) (norm_detectorTaylorPolynomial_le hT hN _ _)
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hn := hg.summable.of_nonneg_of_le (fun j => norm_nonneg _) hb
  calc
    _ ≤ ∑' j : ℕ, ‖(detectorTaylorWeight β (j+J) : ℂ)*detectorTaylorPolynomial T N (j+J) t‖ := norm_tsum_le_tsum_norm hn
    _ ≤ _ := (hn.tsum_le_tsum hb hg.summable).trans_eq (by rw [hg.tsum_eq]; norm_num; ring)

end MathCollab.Density
