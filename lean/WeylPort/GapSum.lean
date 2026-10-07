module
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Tactic

@[expose] public section

open Finset
open scoped BigOperators

namespace WeylPort

/-- Coarse logarithmic control with a fixed lower gap from the last frequency.
This replaces the arithmetic estimate that specialized the dual AFE cutoff to
a half-integer. No half-integer hypothesis on `y` is needed. -/
theorem quadratic_gap_sum_le (y : ℝ) (N : ℕ) (hy : 1 ≤ y)
    (hgap : (N:ℝ)+1/8 ≤ y) :
    ∑ m ∈ Icc 1 N, (m:ℝ)^2/(y^2*(y-m)) ≤ 8*(1+Real.log y) := by
  have hy0 : 0 < y := by linarith
  have hterm (m : ℕ) (hm : m ∈ Icc 1 N) :
      (m:ℝ)^2/(y^2*(y-m)) ≤ 8*(1/((N+1-m:ℕ):ℝ)) := by
    obtain ⟨hm1,hmN⟩ := mem_Icc.mp hm
    have hm0 : (0:ℝ) ≤ m := by positivity
    have hmle : (m:ℝ) ≤ N := by exact_mod_cast hmN
    have hmy : (m:ℝ) < y := by linarith
    have hden : 0 < y-m := by linarith
    have hnat : m ≤ N+1 := by omega
    have he : ((N+1-m:ℕ):ℝ) = (N:ℝ)+1-m := by
      rw [Nat.cast_sub hnat, Nat.cast_add, Nat.cast_one]
    have hpos : 0 < ((N+1-m:ℕ):ℝ) := by rw [he]; linarith
    calc
      _ ≤ 1/(y-m) := by
        apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hy0) hden)).mpr
        have hs : (m:ℝ)^2 ≤ y^2 := pow_le_pow_left₀ hm0 hmy.le 2
        field_simp
        nlinarith
      _ ≤ 8*(1/((N+1-m:ℕ):ℝ)) := by
        rw [mul_one_div, div_le_div_iff₀ hden hpos, he]
        linarith
  have hrev : (∑ m ∈ Icc 1 N, 1/((N+1-m:ℕ):ℝ)) = (harmonic N:ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
    apply sum_bij (fun m _ => N+1-m)
    · intro m hm
      simp only [mem_Icc] at hm ⊢
      omega
    · intro a ha b hb he
      simp only [mem_Icc] at ha hb
      omega
    · intro b hb
      simp only [mem_Icc] at hb
      refine ⟨N+1-b, ?_, ?_⟩
      · simp only [mem_Icc]; omega
      · omega
    · intro m _
      rfl
  have hN : N ≤ ⌊y⌋₊ := Nat.le_floor (by linarith)
  have hmono : (harmonic N:ℝ) ≤ harmonic ⌊y⌋₊ := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · exact Icc_subset_Icc le_rfl hN
    · intro _ _ _; positivity
  calc
    _ ≤ ∑ m ∈ Icc 1 N, 8*(1/((N+1-m:ℕ):ℝ)) := sum_le_sum hterm
    _ = 8*(harmonic N:ℝ) := by rw [← mul_sum, hrev]
    _ ≤ 8*(1+Real.log y) :=
      mul_le_mul_of_nonneg_left (hmono.trans (harmonic_floor_le_one_add_log y hy)) (by norm_num)

end WeylPort
