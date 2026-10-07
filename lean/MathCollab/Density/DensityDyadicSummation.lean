module
public import MathCollab.Density.ZetaConjugation
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

open Real Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The finite bounded-height range is absorbed before all positive scales. -/
theorem zetaSlab_extend_power_bound {σ p C : ℝ} (hp : 0 < p) (hC : 0 < C)
    (hlarge : ∀ᶠ T : ℝ in atTop, (zetaSlabCount σ T (2*T) : ℝ) ≤ C*T^p) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 1 ≤ T →
      (zetaSlabCount σ T (2*T) : ℝ) ≤ A*T^p := by
  obtain ⟨D,hD⟩ := eventually_atTop.mp hlarge
  let R : ℝ := max 1 D
  let Q : ℝ := zetaSlabCount σ 0 (2*R)
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  refine ⟨C+Q, by positivity, ?_⟩
  intro T hT
  by_cases hRT : R ≤ T
  · exact (hD T ((le_max_right _ _).trans hRT)).trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+Q) (by positivity))
  · have hsmall : (zetaSlabCount σ T (2*T) : ℝ) ≤ Q := by
      dsimp [Q]
      exact_mod_cast zetaSlabCount_mono (σ := σ) (σ' := σ) (a := T) (a' := 0)
        (b := 2*T) (b' := 2*R) le_rfl (by linarith) (by linarith [not_le.mp hRT])
    have hpow := Real.one_le_rpow hT hp.le
    exact hsmall.trans (by nlinarith)

/-- Dyadic accumulation with a geometric constant, without spending epsilon. -/
theorem zetaPositive_bound_of_slabs {σ p C : ℝ} (hp : 0 < p) (hC : 0 < C)
    (hslab : ∀ T : ℝ, 1 ≤ T → (zetaSlabCount σ T (2*T) : ℝ) ≤ C*T^p) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 1 ≤ T →
      (zetaSlabCount σ 0 T : ℝ) ≤ A*T^p := by
  let r : ℝ := (2 : ℝ)^p
  let Q : ℝ := zetaSlabCount σ 0 1
  let A : ℝ := Q+C/(r-1)
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hp
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have hA : 0 < A := by dsimp [A]; positivity
  have hAr : A+C ≤ A*r := by
    have he : A*(r-1) = Q*(r-1)+C := by
      dsimp [A]
      rw [add_mul, div_mul_cancel₀ C (by linarith : r-1 ≠ 0)]
    nlinarith [mul_nonneg hQ (show 0 ≤ r-1 by linarith)]
  have hdyadic (k : ℕ) : (zetaSlabCount σ 0 ((2 : ℝ)^k) : ℝ) ≤ A*((2 : ℝ)^k)^p := by
    induction k with
    | zero =>
      simp only [pow_zero, Real.one_rpow, mul_one]
      change Q ≤ A
      dsimp [A]
      exact le_add_of_nonneg_right (by positivity)
    | succ k ih =>
      have h2 : 1 ≤ (2 : ℝ)^k := one_le_pow₀ (by norm_num)
      have hs := hslab ((2 : ℝ)^k) h2
      have hsplit : (zetaSlabCount σ 0 ((2 : ℝ)^(k+1)) : ℝ) ≤
          (zetaSlabCount σ 0 ((2 : ℝ)^k) : ℝ)+(zetaSlabCount σ ((2 : ℝ)^k) (2*2^k) : ℝ) := by
        have hh := zetaSlabCount_split_le σ 0 ((2 : ℝ)^k) (2*2^k)
        rw [show (2 : ℝ)^(k+1) = 2*2^k by ring]
        exact_mod_cast hh
      calc
        _ ≤ _ := hsplit
        _ ≤ A*((2 : ℝ)^k)^p+C*((2 : ℝ)^k)^p := add_le_add ih hs
        _ = (A+C)*((2 : ℝ)^k)^p := by ring
        _ ≤ (A*r)*((2 : ℝ)^k)^p := mul_le_mul_of_nonneg_right hAr (by positivity)
        _ = A*((2 : ℝ)^(k+1))^p := by
          rw [pow_succ, Real.mul_rpow (by positivity) (by norm_num)]
          dsimp [r]
          ring
  refine ⟨A*r, by positivity, ?_⟩
  intro T hT
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near hT (by norm_num : (1 : ℝ) < 2)
  have hm : (zetaSlabCount σ 0 T : ℝ) ≤ (zetaSlabCount σ 0 ((2 : ℝ)^(k+1)) : ℝ) := by
    exact_mod_cast zetaSlabCount_mono (σ := σ) (σ' := σ) (a := 0) (a' := 0) le_rfl le_rfl hhi.le
  have hpow : ((2 : ℝ)^(k+1))^p ≤ (2*T)^p := by
    apply Real.rpow_le_rpow (by positivity) _ hp.le
    rw [pow_succ]
    linarith
  calc
    _ ≤ A*((2 : ℝ)^(k+1))^p := hm.trans (hdyadic (k+1))
    _ ≤ A*(2*T)^p := mul_le_mul_of_nonneg_left hpow hA.le
    _ = (A*r)*T^p := by rw [Real.mul_rpow (by norm_num) (by linarith : 0 ≤ T)]; dsimp [r]; ring

/-- Eventual positive-slab bounds imply a uniform bound for the original count
of all actual zeros, with analytic multiplicity and both closed endpoints. -/
theorem zetaDensity_bound_of_eventual_slabs {σ p C : ℝ}
    (hp : 0 < p) (hC : 0 < C)
    (hslab : ∀ᶠ T : ℝ in atTop, (zetaSlabCount σ T (2*T) : ℝ) ≤ C*T^p) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 2 ≤ T →
      (zetaDensityCount σ T : ℝ) ≤ A*T^p := by
  obtain ⟨B,hB,hall⟩ := zetaSlab_extend_power_bound hp hC hslab
  obtain ⟨D,hD,hpos⟩ := zetaPositive_bound_of_slabs hp hB hall
  refine ⟨2*D, by positivity, ?_⟩
  intro T hT
  have hsym : (zetaDensityCount σ T : ℝ) ≤ 2*(zetaSlabCount σ 0 T : ℝ) := by
    exact_mod_cast zetaDensityCount_le_twice_positive σ T
  have hb := hpos T (by linarith)
  nlinarith

end MathCollab.Density
