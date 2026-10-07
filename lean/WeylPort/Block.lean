module
public import GuthMaynard.WeylZeta

@[expose] public section

/-!
# Classical Weyl cancellation on physical critical-line blocks

This reparametrizes McColm's proved finite block estimate by the actual height `t`.
It does not assert a bound on `riemannZeta`; a short approximate functional
equation is still needed for that theorem.
-/

open Complex Finset
open scoped BigOperators

namespace WeylPort

/-- The actual critical-line Dirichlet block has Weyl size in the medium range.
The block is `[A, A + N)`, with `t^(1/3) ≤ A ≤ sqrt t` and `N ≤ A`.
No analytic bound is a hypothesis. -/
theorem norm_criticalLine_cpow_block_le
    (t : ℝ) (A N : ℕ) (ht : 1 ≤ t) (hA : 0 < A)
    (hlo : t ^ (1 / 3 : ℝ) ≤ A) (hhi : (A : ℝ) ^ 2 ≤ t) (hN : N ≤ A) :
    ‖∑ n ∈ Finset.range N,
      (A + n : ℂ) ^ (-((1 / 2 : ℂ) + (t : ℂ) * I))‖ ≤
      30 * t ^ (1 / 6 : ℝ) := by
  have ht0 : 0 ≤ t := by linarith
  let Y : ℝ := t ^ (1 / 3 : ℝ)
  have hY : 1 ≤ Y := Real.one_le_rpow ht (by norm_num)
  have hcube : Y ^ 3 = t := by
    dsimp only [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
    norm_num
  have hsqrt : Real.sqrt Y = t ^ (1 / 6 : ℝ) := by
    dsimp only [Y]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht0]
    norm_num
  by_cases hNz : N = 0
  · subst N
    simp only [Finset.sum_range_zero, norm_zero]
    positivity
  have hb := RiemannZeta.GuthMaynard.norm_criticalLineWeylBlock_le
    Y A N hY hA (Nat.pos_of_ne_zero hNz) hlo (hcube ▸ hhi) hN
  rw [RiemannZeta.GuthMaynard.criticalLineWeylBlock_eq_cpow Y A N hA] at hb
  simpa only [← Complex.ofReal_pow, hcube, hsqrt] using hb

end WeylPort
