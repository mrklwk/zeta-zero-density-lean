module
/-
Adapted from selected proofs in Scott McColm's ZeroCount.lean at
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be; MIT.
No upstream zero-count definition or project module is imported.
-/
public import MathCollab.Density.AbelZetaGrowth
public import MathCollab.Density.ZetaCounting
public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open Complex Filter MeromorphicOn
open scoped Topology ArithmeticFunction.Moebius ComplexOrder

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density.ZetaGrowth

theorem finset_analyticOrderNatAt_le_finsum_divisor {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsCompact U) (hpre : IsPreconnected U)
    {c : ℂ} (hc : c ∈ U) (hcOrder : analyticOrderAt f c ≠ ⊤)
    (S : Finset ℂ) (hSU : ∀ u ∈ S, u ∈ U) :
    ((∑ u ∈ S, analyticOrderNatAt f u : ℕ) : ℝ) ≤
      ((∑ᶠ u, divisor f U u : ℤ) : ℝ) := by
  let g : ℂ → ℝ := fun u => if u ∈ S then (analyticOrderNatAt f u : ℝ) else 0
  let d : ℂ → ℝ := fun u => (divisor f U u : ℝ)
  have hgFin : Function.HasFiniteSupport g := by
    apply Set.Finite.subset S.finite_toSet
    intro u hu
    simp only [Function.mem_support, ne_eq] at hu
    by_contra huS
    have huS' : u ∉ S := by simpa using huS
    exact hu (by simp [g, huS'])
  have hdFin : Function.HasFiniteSupport d := by
    have hfin := (divisor f U).finiteSupport hU
    exact hfin.subset (by
      intro u hu
      simpa only [Function.mem_support, d, Int.cast_eq_zero, ne_eq] using hu)
  have hgd : g ≤ d := by
    intro u
    by_cases huS : u ∈ S
    · have huU := hSU u huS
      have huOrder := hf.analyticOrderAt_ne_top_of_isPreconnected hpre hc huU hcOrder
      simp only [g, d, ite_eq_left huS]
      rw [hf.divisor_apply huU, ← Nat.cast_analyticOrderNatAt huOrder]
      simp
    · simp only [g, ite_eq_right huS]
      change 0 ≤ (divisor f U u : ℝ)
      exact_mod_cast hf.divisor_nonneg u
  have hle := finsum_le_finsum hgFin hdFin hgd
  have hgSum : ∑ᶠ u, g u = ∑ u ∈ S, g u :=
    finsum_eq_sum_of_support_subset g (by
      intro u hu
      simp only [Function.mem_support, ne_eq] at hu
      by_contra huS
      have huS' : u ∉ S := by simpa using huS
      exact hu (by simp [g, huS']))
  have hdSum : ((∑ᶠ u, divisor f U u : ℤ) : ℝ) = ∑ᶠ u, d u := by
    simpa [d] using map_finsum (Int.castRingHom ℝ) ((divisor f U).finiteSupport hU)
  change ((∑ u ∈ S, analyticOrderNatAt f u : ℕ) : ℝ) ≤ _
  calc
    ((∑ u ∈ S, analyticOrderNatAt f u : ℕ) : ℝ) = ∑ u ∈ S, g u := by simp [g]
    _ = ∑ᶠ u, g u := hgSum.symm
    _ ≤ ∑ᶠ u, d u := hle
    _ = ((∑ᶠ u, divisor f U u : ℤ) : ℝ) := hdSum.symm

theorem zeta_jensen_sphere_bound (T t : ℝ) (hT : T ≥ 8)
    (ht : t ∈ Set.Icc (T - 1) (2 * T)) :
    ∀ z ∈ Metric.sphere (2 + I * (t + 1/2)) (7/4),
      ‖riemannZeta z‖ ≤ 100 * T ^ (3:ℝ) := by
  intro z hz
  rw [Metric.mem_sphere, dist_eq_norm] at hz
  let c : ℂ := 2 + I * (t + 1/2)
  have hzc : ‖z - c‖ = 7 / 4 := by simpa [c] using hz
  have hreDiff : |z.re - 2| ≤ 7 / 4 := by
    calc
      |z.re - 2| = |(z - c).re| := by simp [c]
      _ ≤ ‖z - c‖ := abs_re_le_norm _
      _ = 7 / 4 := hzc
  have himDiff : |z.im - (t + 1/2)| ≤ 7 / 4 := by
    calc
      |z.im - (t + 1/2)| = |(z - c).im| := by simp [c]
      _ ≤ ‖z - c‖ := abs_im_le_norm _
      _ = 7 / 4 := hzc
  have hre : (1 / 4 : ℝ) ≤ z.re := by
    have := (abs_le.mp hreDiff).1
    linarith
  have himPos : 1 ≤ z.im := by
    have := (abs_le.mp himDiff).1
    linarith [ht.1]
  have him : 1 ≤ |z.im| := himPos.trans (le_abs_self z.im)
  have hcNorm : ‖c‖ ≤ t + 5/2 := by
    calc
      ‖c‖ ≤ ‖(2 : ℂ)‖ + ‖I * ((t + 1/2 : ℝ) : ℂ)‖ := by
        simpa [c] using norm_add_le (2 : ℂ) (I * ((t + 1/2 : ℝ) : ℂ))
      _ = 2 + ‖((t + 1/2 : ℝ) : ℂ)‖ := by simp
      _ = 2 + |t + 1/2| := by rw [norm_real, Real.norm_eq_abs]
      _ = t + 5/2 := by
        rw [abs_of_nonneg]
        · ring
        · linarith [ht.1]
  have hzNorm : ‖z‖ ≤ 3 * T := by
    calc
      ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
      _ = 7/4 + ‖c‖ := by rw [hzc]
      _ ≤ 7/4 + (t + 5/2) := by gcongr
      _ ≤ 3 * T := by linarith [ht.2]
  calc
    ‖riemannZeta z‖ ≤ 5 * ‖z‖ := norm_riemannZeta_le_five_mul_norm hre him
    _ ≤ 15 * T := by nlinarith [norm_nonneg z]
    _ ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT0 : 0 ≤ T := by linarith
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        15 * T ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring

theorem moebius_coeff_norm_le_one (n : ℕ) :
    ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ ‖(1 : ℂ)‖ := by
  rw [Complex.norm_intCast, norm_one]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)

/-- On the line `Re(s) = 2`, the Möbius Dirichlet series has norm less than
`5 / 3`, by comparison with `ζ(2) = π² / 6`. -/
theorem moebius_LSeries_norm_lt_five_thirds (u : ℝ) :
    ‖LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 + u * I)‖ <
      (5 / 3 : ℝ) := by
  let s : ℂ := 2 + u * I
  have hsRe : s.re = 2 := by simp [s]
  have hs : 1 < s.re := by rw [hsRe]; norm_num
  have hSumM : LSeriesSummable
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hSumTwo : LSeriesSummable 1 (2 : ℂ) :=
    LSeriesSummable_one_iff.mpr (by norm_num)
  rw [LSeries]
  calc
    ‖∑' n, LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ ≤
        ∑' n, ‖LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ :=
      norm_tsum_le_tsum_norm hSumM.norm
    _ ≤ ∑' n, ‖LSeries.term 1 (2 : ℂ) n‖ := by
      apply hSumM.norm.tsum_le_tsum _ hSumTwo.norm
      intro n
      calc
        ‖LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s n‖ ≤
            ‖LSeries.term 1 s n‖ :=
          LSeries.norm_term_le s (moebius_coeff_norm_le_one n)
        _ = ‖LSeries.term 1 (2 : ℂ) n‖ := by
          rw [LSeries.norm_term_eq, LSeries.norm_term_eq, hsRe]
          norm_num
    _ = (LSeries 1 (2 : ℂ)).re := by
      rw [LSeries, Complex.re_tsum hSumTwo]
      apply tsum_congr
      intro n
      have hn : (0 : ℂ) ≤ LSeries.term 1 (2 : ℝ) n :=
        LSeries.term_nonneg (by simp) 2
      have heq := congrArg Complex.re (Complex.norm_of_nonneg' hn)
      simpa using heq
    _ = Real.pi ^ 2 / 6 := by
      rw [LSeries_one_eq_riemannZeta (by norm_num), riemannZeta_two]
      norm_cast
    _ < 5 / 3 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-- Lower bound on the line `Re(s) = 2`, obtained from the absolutely
convergent Möbius inverse of the zeta Dirichlet series. -/
theorem euler_product_lower_bound_2 (t : ℝ) :
    (0.6 : ℝ) ≤ ‖riemannZeta (2 + I * (t + 1 / 2))‖ := by
  let s : ℂ := 2 + I * (t + 1 / 2)
  have hsRe : s.re = 2 := by simp [s]
  have hs : 1 < s.re := by rw [hsRe]; norm_num
  have hprod :
      riemannZeta s * LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s = 1 := by
    rw [← LSeries_one_eq_riemannZeta hs]
    exact LSeries_one_mul_Lseries_moebius hs
  have hnormprod := congrArg norm hprod
  rw [norm_mul, norm_one] at hnormprod
  have hM : ‖LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ ≤ 5 / 3 := by
    have h := moebius_LSeries_norm_lt_five_thirds (t + 1 / 2)
    simpa [s, mul_comm] using h.le
  have hone : (1 : ℝ) ≤ ‖riemannZeta s‖ * (5 / 3) := by
    calc
      (1 : ℝ) = ‖riemannZeta s‖ *
          ‖LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) s‖ := hnormprod.symm
      _ ≤ ‖riemannZeta s‖ * (5 / 3) := by gcongr
  change (0.6 : ℝ) ≤ ‖riemannZeta s‖
  nlinarith [norm_nonneg (riemannZeta s)]


end MathCollab.Density.ZetaGrowth
