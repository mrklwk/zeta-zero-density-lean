module
public import MathCollab.Density.ProductGrouping
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

open Real Set
open scoped BigOperators

set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- A geometric majorant bounds every prime-power exponent uniformly. -/
theorem exponent_linear_le_geometric {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ e : ℕ, (e : ℝ)+1 ≤ C*((2 : ℝ)^η)^e := by
  let r := ((2 : ℝ)^η)⁻¹
  have hp : 1 < (2 : ℝ)^η := Real.one_lt_rpow (by norm_num) hη
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hp
  have hrn : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr]
  have hs : Summable (fun e : ℕ => ((e : ℝ)+1)*r^e) := by
    have hh := (summable_pow_mul_geometric_of_norm_lt_one 1 hrn).add
      (summable_geometric_of_norm_lt_one hrn)
    simpa only [pow_one, add_mul, one_mul] using hh
  let C := ∑' e : ℕ, ((e : ℝ)+1)*r^e
  have hle (e : ℕ) : ((e : ℝ)+1)*r^e ≤ C := hs.le_tsum e (fun _ _ => by positivity)
  refine ⟨C, ?_, ?_⟩
  · simpa only [Nat.cast_zero, zero_add, pow_zero, mul_one] using hle 0
  · intro e
    have hh := hle e
    dsimp [r] at hh
    rw [inv_pow, ← div_eq_mul_inv] at hh
    exact (div_le_iff₀ (by positivity)).1 hh

theorem exponent_linear_le_two_pow (e : ℕ) : (e : ℝ)+1 ≤ (2 : ℝ)^e := by
  induction e with
  | zero => norm_num
  | succ e ih =>
    have hh : (1 : ℝ) ≤ (2 : ℝ)^e := one_le_pow₀ (by norm_num)
    push_cast
    rw [pow_succ]
    linarith

/-- The divisor-growth constant depends on eta alone, before every integer n. -/
theorem divisor_card_subpower {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, 0 < n → (n.divisors.card : ℝ) ≤ C*(n : ℝ)^η := by
  obtain ⟨C, hC, h_exp⟩ := exponent_linear_le_geometric hη
  let K := ⌈(2 : ℝ)^(1/η)⌉₊
  have hCp : 0 < C := by linarith
  have hprime (p e : ℕ) (hp : p.Prime) :
      (e : ℝ)+1 ≤ (if p ≤ K then C else 1)*((p : ℝ)^η)^e := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpη : (2 : ℝ)^η ≤ (p : ℝ)^η := Real.rpow_le_rpow (by norm_num) hp2 hη.le
    by_cases hpk : p ≤ K
    · rw [ite_eq_left hpk]
      exact (h_exp e).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hpη e) hCp.le)
    · rw [ite_eq_right hpk, one_mul]
      have hlarge : (2 : ℝ)^(1/η) ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hpk)))
      have hh := Real.rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ)^(1/η)) hlarge hη.le
      have he : ((2 : ℝ)^(1/η))^η = 2 := by
        rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        rw [div_mul_cancel₀ 1 hη.ne', Real.rpow_one]
      rw [he] at hh
      exact (exponent_linear_le_two_pow e).trans (pow_le_pow_left₀ (by norm_num) hh e)
  refine ⟨C^K, one_le_pow₀ hC, ?_⟩
  intro n hn
  have hprod : (∏ p ∈ n.primeFactors, ((p : ℝ)^η)^n.factorization p) = (n : ℝ)^η := by
    have hnprod : (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ)^n.factorization p := by
      exact_mod_cast Nat.prod_primeFactors_pow_factorization hn.ne'
    rw [hnprod, ← Real.finsetProd_rpow]
    · apply Finset.prod_congr rfl
      intro p hp
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
        Real.rpow_mul (by positivity), Real.rpow_natCast]
    · intro p hp
      positivity
  have hcount : (n.primeFactors.filter (fun p => p ≤ K)).card ≤ K := by
    have hs : n.primeFactors.filter (fun p => p ≤ K) ⊆ Finset.Icc 1 K := by
      intro p hp
      obtain ⟨hpn, hpK⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hpn).pos, hpK⟩
    exact (Finset.card_le_card hs).trans_eq (by simp)
  calc
    _ = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ)+1) := by
      rw [Nat.card_divisors hn.ne']
      push_cast
      rfl
    _ ≤ ∏ p ∈ n.primeFactors, (if p ≤ K then C else 1)*((p : ℝ)^η)^n.factorization p :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity)
        (fun p hp => hprime p _ (Nat.prime_of_mem_primeFactors hp))
    _ = (∏ p ∈ n.primeFactors, if p ≤ K then C else 1)*(n : ℝ)^η := by
      rw [Finset.prod_mul_distrib, hprod]
    _ = C^((n.primeFactors.filter (fun p => p ≤ K)).card)*(n : ℝ)^η := by
      rw [Finset.prod_ite]
      simp only [Finset.prod_const, one_pow, mul_one]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC hcount) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The ceiling cutoff is controlled uniformly for T at least two. -/
theorem divisorMaximum_subpower {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ T : ℝ, 2 ≤ T → (divisorMaximum T : ℝ) ≤ C*T^η := by
  obtain ⟨C, hC, hd⟩ := divisor_card_subpower hη
  have h49 : (1 : ℝ) ≤ 49^η := Real.one_le_rpow (by norm_num) hη.le
  refine ⟨C*49^η, by nlinarith, ?_⟩
  intro T hT
  have hTp : 0 < T := by linarith
  have hcut : (⌈32*(T+1)⌉₊ : ℝ) ≤ 49*T := by
    have hh := Nat.ceil_lt_add_one (show 0 ≤ 32*(T+1) by linarith)
    linarith
  have hbound (m : ℕ) (hm : m ∈ Finset.Icc 1 ⌈32*(T+1)⌉₊) :
      (m.divisors.card : ℝ) ≤ C*49^η*T^η := by
    have hm' := Finset.mem_Icc.mp hm
    have hmT : (m : ℝ) ≤ 49*T := (by exact_mod_cast hm'.2 : (m : ℝ) ≤ (⌈32*(T+1)⌉₊ : ℝ)).trans hcut
    calc
      _ ≤ C*(m : ℝ)^η := hd m hm'.1
      _ ≤ C*(49*T)^η := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hmT hη.le) (by linarith)
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 49) hTp.le]; ring
  have hle : divisorMaximum T ≤ ⌊C*49^η*T^η⌋₊ := by
    apply Finset.sup_le
    intro m hm
    exact Nat.le_floor (hbound m hm)
  exact (by exact_mod_cast hle : (divisorMaximum T : ℝ) ≤ (⌊C*49^η*T^η⌋₊ : ℝ)).trans
    (Nat.floor_le (by positivity))

end MathCollab.Density
