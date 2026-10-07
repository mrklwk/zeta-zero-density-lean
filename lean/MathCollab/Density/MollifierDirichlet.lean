module
/-
Finite-support Dirichlet product proofs adapted from McColm ClassicalDensity,
exact pin 2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, MIT.
The existing real floor-cutoff mollifier and integer coefficients are preserved.
-/
public import MathCollab.Density.MollifierCoefficients
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

@[expose] public section

open Complex Finset Filter
open scoped ArithmeticFunction.Moebius BigOperators
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Complex coercion of the existing integer coefficient, with no new cutoff. -/
def mollifierDirichletCoeff (X : ℝ) (n : ℕ) : ℂ := (mollifierCoefficient X n : ℂ)

/-- The finite Möbius mollifier as an arithmetic function. -/
noncomputable def truncatedMoebius (X : ℝ) : ArithmeticFunction ℂ where
  toFun n := if n ∈ Icc 1 ⌊X⌋₊ then
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) else 0
  map_zero' := by simp

@[simp]
theorem truncatedMoebius_apply (X : ℝ) (n : ℕ) :
    truncatedMoebius X n = if n ∈ Icc 1 ⌊X⌋₊ then
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) else 0 := rfl

theorem truncatedMoebius_hasFiniteSupport (X : ℝ) :
    Function.HasFiniteSupport (truncatedMoebius X) := by
  apply Set.Finite.subset (Icc 1 ⌊X⌋₊).finite_toSet
  intro n hn
  simp only [Function.mem_support, ne_eq] at hn
  by_contra hnMem
  have hnMem' : n ∉ Icc 1 ⌊X⌋₊ := by simpa using hnMem
  exact hn (by rw [truncatedMoebius_apply, ite_eq_right hnMem'])

theorem truncatedMoebius_LSeriesSummable (X : ℝ) (s : ℂ) :
    LSeriesSummable (truncatedMoebius X) s := by
  unfold LSeriesSummable
  exact summable_of_hasFiniteSupport <|
    (truncatedMoebius_hasFiniteSupport X).subset (by
      intro n hn
      simp only [Function.mem_support, ne_eq] at hn ⊢
      contrapose! hn
      rw [LSeries.term_def₀ (truncatedMoebius X).map_zero]
      simp [hn])

/-- The finite-sum definition of the mollifier agrees exactly with its
L-series representation. -/
theorem zetaMollifier_eq_LSeries (X : ℝ) (s : ℂ) :
    zetaMollifier X s = LSeries (truncatedMoebius X) s := by
  rw [zetaMollifier, LSeries, tsum_eq_sum (s := Icc 1 ⌊X⌋₊)]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [LSeries.term_def₀ (truncatedMoebius X).map_zero]
    simp only [truncatedMoebius_apply, ite_eq_left hn]
  · intro n hn
    rw [LSeries.term_def₀ (truncatedMoebius X).map_zero]
    simp [hn]

/-- Multiplication by zeta produces the truncated divisor-sum coefficient. -/
theorem zeta_mul_truncatedMoebius_apply (X : ℝ) (n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) * truncatedMoebius X) n =
      mollifierDirichletCoeff X n := by
  rw [ArithmeticFunction.coe_zeta_mul_apply]
  simp only [truncatedMoebius_apply, mollifierDirichletCoeff, mollifierCoefficient, Int.cast_sum]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext d
    simp only [Finset.mem_filter, and_congr_right_iff]
    intro hd
    have hdData := Nat.mem_divisors.mp hd
    have hdNe : d ≠ 0 := ne_zero_of_dvd_ne_zero hdData.2 hdData.1
    simp [Nat.one_le_iff_ne_zero.mpr hdNe]
  · intro d hd
    simp only [Finset.mem_filter] at hd
    simp

/-- In the half-plane of absolute convergence, the analytic mollified zeta
product is the L-series with the truncated Möbius divisor coefficients. -/
theorem riemannZeta_mul_zetaMollifier_eq_LSeries (X : ℝ) {s : ℂ}
    (hs : 1 < s.re) :
    riemannZeta s * zetaMollifier X s = LSeries (mollifierDirichletCoeff X) s := by
  have hProd :
      LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        truncatedMoebius X) n) s =
      LSeries (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s *
        LSeries (fun n => truncatedMoebius X n) s :=
    ArithmeticFunction.LSeries_mul'
      (f := (ArithmeticFunction.zeta : ArithmeticFunction ℂ))
      (g := truncatedMoebius X) (s := s)
      (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
      (truncatedMoebius_LSeriesSummable X s)
  have hZeta :
      LSeries (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s =
        riemannZeta s := by
    simpa only [ArithmeticFunction.natCoe_apply] using
      ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  calc
    riemannZeta s * zetaMollifier X s =
        LSeries (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s *
          LSeries (fun n => truncatedMoebius X n) s := by
      rw [hZeta, ← zetaMollifier_eq_LSeries]
    _ = LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
        truncatedMoebius X) n) s := hProd.symm
    _ = LSeries (mollifierDirichletCoeff X) s :=
      LSeries_congr (fun {_n} _hn => zeta_mul_truncatedMoebius_apply X _n) s

theorem mollifierDirichletCoeff_LSeriesSummable (X : ℝ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (mollifierDirichletCoeff X) s := by
  have hMul := ArithmeticFunction.LSeriesSummable_mul
    (f := (ArithmeticFunction.zeta : ArithmeticFunction ℂ))
    (g := truncatedMoebius X) (s := s)
    (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
    (truncatedMoebius_LSeriesSummable X s)
  exact (LSeriesSummable_congr s
    (fun {_n} _hn => zeta_mul_truncatedMoebius_apply X _n)).mp hMul


/-- The zero-index coefficient vanishes independently of the cutoff. -/
theorem mollifierDirichletCoeff_zero (X : ℝ) : mollifierDirichletCoeff X 0 = 0 := by
  simp [mollifierDirichletCoeff, mollifierCoefficient]

/-- A bound uniform in the series index, with the exact finite cutoff. -/
theorem norm_mollifierDirichletCoeff_le_cutoff (X : ℝ) (n : ℕ) :
    ‖mollifierDirichletCoeff X n‖ ≤ (⌊X⌋₊ : ℝ) := by
  let S := n.divisors.filter (fun d => d ≤ ⌊X⌋₊)
  have hsub : S ⊆ Finset.Icc 1 ⌊X⌋₊ := by
    intro d hd
    obtain ⟨hd, hcut⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr
      (ne_zero_of_dvd_ne_zero (Nat.mem_divisors.mp hd).2 (Nat.mem_divisors.mp hd).1), hcut⟩
  have hcard : S.card ≤ ⌊X⌋₊ := by
    simpa using Finset.card_le_card hsub
  calc
    ‖mollifierDirichletCoeff X n‖ = ‖∑ d ∈ S, (ArithmeticFunction.moebius d : ℂ)‖ := by
      simp [mollifierDirichletCoeff, mollifierCoefficient, S]
    _ ≤ ∑ d ∈ S, ‖(ArithmeticFunction.moebius d : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ S, (1 : ℝ) := Finset.sum_le_sum fun d _ => by
      rw [Complex.norm_intCast]
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
    _ = (S.card : ℝ) := by simp
    _ ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hcard

/-- The finite mollifier is entire in its complex argument. -/
theorem differentiableAt_zetaMollifier (X : ℝ) (s : ℂ) :
    DifferentiableAt ℂ (zetaMollifier X) s := by
  unfold zetaMollifier
  apply DifferentiableAt.fun_sum
  intro m hm
  apply (differentiableAt_const (𝕜 := ℂ) ((ArithmeticFunction.moebius m : ℂ))).mul
  have hmZero : (m : ℂ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 from Nat.ne_zero_of_lt (Finset.mem_Icc.mp hm).1)
  exact differentiableAt_id.neg.const_cpow (Or.inl hmZero)

end MathCollab.Density
