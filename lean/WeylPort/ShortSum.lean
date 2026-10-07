module
public import WeylPort.Block
public import WeylPort.GrowthAlgebra
public import Mathlib.Data.Nat.Log

@[expose] public section

open Complex Finset
open scoped BigOperators

namespace WeylPort

noncomputable def criticalTerm (t : ℝ) (n : ℕ) : ℂ :=
  (n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I))

theorem norm_criticalTerm (t : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖criticalTerm t n‖ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold criticalTerm
  rw [Complex.norm_natCast_cpow_of_pos hn]
  congr 1
  simp

/-- Absolute estimation handles every block below the cube-root height. -/
theorem norm_critical_block_small (t : ℝ) (A N : ℕ)
    (ht : 0 ≤ t) (hA : 0 < A) (hNA : N ≤ A)
    (hsmall : (A : ℝ) ≤ t ^ (1 / 3 : ℝ)) :
    ‖∑ n ∈ range N, criticalTerm t (A+n)‖ ≤ t ^ (1 / 6 : ℝ) := by
  have hApos : 0 < (A : ℝ) := by exact_mod_cast hA
  calc
    _ ≤ ∑ n ∈ range N, ‖criticalTerm t (A+n)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ range N, (A : ℝ) ^ (-(1 / 2 : ℝ)) := by
      apply sum_le_sum
      intro n _hn
      rw [norm_criticalTerm t (by omega)]
      exact Real.rpow_le_rpow_of_nonpos hApos (by norm_num) (by norm_num)
    _ = (N : ℝ) * (A : ℝ) ^ (-(1 / 2 : ℝ)) := by simp
    _ ≤ (A : ℝ) * (A : ℝ) ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hNA) (by positivity)
    _ = (A : ℝ) ^ (1 / 2 : ℝ) := by
      conv_lhs => lhs; rw [← Real.rpow_one (A : ℝ)]
      rw [← Real.rpow_add hApos]
      norm_num
    _ ≤ (t ^ (1 / 3 : ℝ)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hApos.le hsmall (by norm_num)
    _ = t ^ (1 / 6 : ℝ) := by rw [← Real.rpow_mul ht]; norm_num

/-- Uniform Weyl bound on all blocks up to the square-root length. -/
theorem norm_critical_block_le (t : ℝ) (A N : ℕ)
    (ht : 1 ≤ t) (hA : 0 < A) (hNA : N ≤ A) (hAt : (A : ℝ)^2 ≤ t) :
    ‖∑ n ∈ range N, criticalTerm t (A+n)‖ ≤ 30 * t ^ (1 / 6 : ℝ) := by
  by_cases hlo : t ^ (1 / 3 : ℝ) ≤ A
  · simpa only [criticalTerm, Nat.cast_add] using
      norm_criticalLine_cpow_block_le t A N ht hA hlo hAt hNA
  · have hb := norm_critical_block_small t A N (by linarith) hA hNA
      (le_of_not_ge hlo)
    have hp : 0 ≤ t ^ (1 / 6 : ℝ) := Real.rpow_nonneg (by linarith) _
    linarith

/-- At most `K` dyadic blocks suffice for every prefix shorter than `2^K`. -/
theorem norm_critical_sum_le_dyadic (t : ℝ) (K N : ℕ)
    (ht : 1 ≤ t) (hNK : N < 2^K) (hNt : (N : ℝ)^2 ≤ t) :
    ‖∑ n ∈ Ico 1 (N+1), criticalTerm t n‖ ≤ 30 * K * t ^ (1 / 6 : ℝ) := by
  induction K generalizing N with
  | zero =>
    have hN : N = 0 := by simpa using hNK
    subst N
    simp
  | succ K ih =>
    have hp : 0 ≤ t ^ (1 / 6 : ℝ) := Real.rpow_nonneg (by linarith) _
    by_cases hsmall : N < 2^K
    · have hb := ih N hsmall hNt
      push_cast
      nlinarith
    · have hApos : 0 < (2:ℕ)^K := by positivity
      have hAN : (2:ℕ)^K ≤ N := by omega
      have hArN : ((2:ℕ)^K : ℝ) ≤ N := by exact_mod_cast hAN
      have hAt : (((2:ℕ)^K : ℝ))^2 ≤ t := by
        exact (pow_le_pow_left₀ (by positivity) hArN 2).trans hNt
      have hheadlt : (2:ℕ)^K - 1 < 2^K := by omega
      have hheadle : (((2:ℕ)^K - 1 : ℕ) : ℝ) ≤ ((2:ℕ)^K : ℝ) := by
        exact_mod_cast Nat.sub_le ((2:ℕ)^K) 1
      have hhead := ih ((2:ℕ)^K-1) hheadlt
        ((pow_le_pow_left₀ (by positivity) hheadle 2).trans hAt)
      have htop : (2:ℕ)^K - 1 + 1 = 2^K := by omega
      rw [htop] at hhead
      have hlength : N + 1 - (2:ℕ)^K ≤ 2^K := by
        rw [pow_succ] at hNK
        omega
      have htail := norm_critical_block_le t (2^K) (N+1-2^K) ht hApos hlength
        (by simpa only [Nat.cast_pow] using hAt)
      rw [← sum_Ico_eq_sum_range] at htail
      rw [← sum_Ico_consecutive (criticalTerm t) (by omega : 1 ≤ (2:ℕ)^K)
        (by omega : (2:ℕ)^K ≤ N+1)]
      have hn := norm_add_le (∑ n ∈ Ico 1 (2^K), criticalTerm t n)
        (∑ n ∈ Ico (2^K) (N+1), criticalTerm t n)
      push_cast
      linarith

/-- Explicit bound for every short Dirichlet polynomial on the critical line. -/
theorem norm_critical_sum_le_log (t : ℝ) (N : ℕ)
    (ht : 1 ≤ t) (hNt : (N : ℝ)^2 ≤ t) :
    ‖∑ n ∈ Ico 1 (N+1), criticalTerm t n‖ ≤
      30 * (Real.log t + 1) * t ^ (1 / 6 : ℝ) := by
  by_cases hN : N = 0
  · subst N
    simp only [zero_add, Ico_self, sum_empty, norm_zero]
    have : 0 ≤ Real.log t := Real.log_nonneg ht
    have : 0 ≤ t := by linarith
    positivity
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hpow : (2:ℝ)^(Nat.log 2 N) ≤ N := by
    exact_mod_cast Nat.pow_log_le_self 2 hN
  have hl := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow] at hl
  have hs := Real.log_le_log (sq_pos_of_pos hNpos) hNt
  rw [Real.log_pow] at hs
  norm_num only [Nat.cast_ofNat] at hs
  have htwo : (1/2:ℝ) ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hk : (Nat.log 2 N : ℝ) ≤ Real.log t := by
    have hm := mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg (α := ℝ) (Nat.log 2 N))
    linarith
  have hb := norm_critical_sum_le_dyadic t (Nat.log 2 N+1) N ht
    (Nat.lt_pow_succ_log_self (by norm_num) N) hNt
  have hp : 0 ≤ t ^ (1 / 6 : ℝ) := Real.rpow_nonneg (by linarith) _
  push_cast at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) hp)

/-- A fixed multiplier and the entire logarithmic loss are absorbed by any positive epsilon.
The eventual threshold is chosen before, and uniformly for, every cutoff `N`. -/
theorem eventually_mul_norm_critical_sum_le_rpow (C : ℝ) (hC : 0 ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in Filter.atTop, ∀ N : ℕ, (N : ℝ)^2 ≤ t →
      C * ‖∑ n ∈ Ico 1 (N+1), criticalTerm t n‖ ≤ t ^ (1/6 + ε : ℝ) := by
  have hsmall := TaoTrudgianYang2025.eventually_const_log_pow_le_rpow
    (60*C) (by positivity) 1 hε
  have hlog := Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))
  filter_upwards [hsmall, hlog, Filter.eventually_ge_atTop (1:ℝ)] with t hs hl ht
  intro N hNt
  have htpos : 0 < t := by linarith
  have hcoeff : C * (30 * (Real.log t + 1)) ≤ t^ε := by
    simp only [pow_one] at hs
    have hmul := mul_le_mul_of_nonneg_left hl hC
    nlinarith
  calc
    _ ≤ C * (30 * (Real.log t + 1) * t^(1/6:ℝ)) :=
      mul_le_mul_of_nonneg_left (norm_critical_sum_le_log t N ht hNt) hC
    _ = (C * (30 * (Real.log t + 1))) * t^(1/6:ℝ) := by ring
    _ ≤ t^ε * t^(1/6:ℝ) :=
      mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ = t^(1/6+ε:ℝ) := by rw [← Real.rpow_add htpos]; congr 1; ring

/-- The complete finite-sum Weyl contract, with a cutoff-uniform threshold. -/
theorem exists_critical_sum_le_sixth_power {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t → ∀ N : ℕ, (N : ℝ)^2 ≤ t →
      ‖∑ n ∈ Ico 1 (N+1), criticalTerm t n‖ ≤ t ^ (1/6+ε:ℝ) := by
  have he := eventually_mul_norm_critical_sum_le_rpow 1 (by norm_num) hε
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp he
  refine ⟨max 1 T₁, le_max_left _ _, ?_⟩
  intro t ht N hNt
  simpa only [one_mul] using hT₁ t ((le_max_right _ _).trans ht) N hNt

end WeylPort
