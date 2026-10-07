module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.DampedWeightedKernel
public import WeylPort.AFE.LowerIntegralEstimate

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Actual finite-frequency main terms and integral assembly

The Gamma evaluation is summed over the actual positive integer frequencies.
The harmonic estimate keeps the isolated unit term and the literal cutoff.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex MeasureTheory

/-- The dual polynomial has the source's uniform logarithmic bound, including both strip endpoints. -/
theorem norm_sum_dual_powers_le {σ t y : ℝ} (hσ : 0 ≤ σ) (hy : 1 ≤ y) :
    ‖∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)‖ ≤
      y ^ σ * Real.log y + 1 := by
  let S := Finset.Icc 1 ⌊y⌋₊
  have h1 : 1 ∈ S := Finset.left_mem_Icc.mpr (Nat.floor_pos.mpr hy)
  have hpos (m : ℕ) (hm : m ∈ S) : 0 < (m : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hle (m : ℕ) (hm : m ∈ S) : (m : ℝ) ≤ y :=
    (by exact_mod_cast (Finset.mem_Icc.mp hm).2 : (m : ℝ) ≤ (⌊y⌋₊ : ℝ)).trans
      (Nat.floor_le (by linarith))
  have hterm (m : ℕ) (hm : m ∈ S) :
      ‖(m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)‖ ≤ y ^ σ * (1 / (m : ℝ)) := by
    rw [← Complex.ofReal_natCast, norm_cpow_eq_rpow_re_of_pos (hpos m hm)]
    simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero, one_re]
    rw [Real.rpow_sub (hpos m hm), Real.rpow_one, mul_one_div]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow (hpos m hm).le (hle m hm) hσ)
      (hpos m hm).le
  have hh : (∑ m ∈ S.erase 1, 1 / (m : ℝ)) ≤ Real.log y := by
    have h := sum_reciprocals_floor_le hy
    change (∑ m ∈ S, 1 / (m : ℝ)) ≤ Real.log y + 1 at h
    rw [← Finset.sum_erase_add S _ h1] at h
    norm_num at h
    simpa only [one_div] using h
  calc
    _ ≤ ∑ m ∈ S, ‖(m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)‖ := norm_sum_le _ _
    _ = 1 + ∑ m ∈ S.erase 1, ‖(m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)‖ := by
      rw [← Finset.sum_erase_add S _ h1]
      simp only [Nat.cast_one, one_cpow, norm_one, add_comm]
    _ ≤ 1 + y ^ σ * ∑ m ∈ S.erase 1, 1 / (m : ℝ) := by
      rw [Finset.mul_sum]
      apply add_le_add (le_refl _)
      exact Finset.sum_le_sum (fun m hm => hterm m (Finset.mem_of_mem_erase hm))
    _ ≤ 1 + y ^ σ * Real.log y :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg (by linarith) _))
    _ = _ := by ring

/-- The actual improper integral main terms sum to the exact chi factor times the dual polynomial. -/
theorem sum_weightedIntegralTail_zero_eq_chi {σ t y t₀ : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 (m : ℝ)) =
      chi ((σ : ℂ) + (t : ℂ) * I) * (1 + gammaChiError ((σ : ℂ) + (t : ℂ) * I)) *
        ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  simpa only [Complex.ofReal_natCast] using weightedIntegralTail_zero_eq_chi hσ hmpos ht₀ ht

/-- The error in replacing the actual main integrals by the dual polynomial has the printed logarithmic size. -/
theorem norm_sum_weightedIntegralTail_sub_chi_le {σ t y t₀ : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (hy : 1 ≤ y) (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖(∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 (m : ℝ)) -
      chi ((σ : ℂ) + (t : ℂ) * I) *
        ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)‖ ≤
      ‖chi ((σ : ℂ) + (t : ℂ) * I)‖ *
        (Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))) *
        (y ^ σ * Real.log y + 1) := by
  rw [sum_weightedIntegralTail_zero_eq_chi hσ ht₀ ht]
  rw [show chi ((σ : ℂ) + (t : ℂ) * I) *
      (1 + gammaChiError ((σ : ℂ) + (t : ℂ) * I)) *
      (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)) -
      chi ((σ : ℂ) + (t : ℂ) * I) *
      (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)) =
      chi ((σ : ℂ) + (t : ℂ) * I) * gammaChiError ((σ : ℂ) + (t : ℂ) * I) *
      (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)) by ring,
    norm_mul, norm_mul]
  have he : ‖gammaChiError ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀)) := by
    simpa using norm_gammaChiError_le (s := (σ : ℂ) + (t : ℂ) * I) ht₀ (by simpa using ht)
  exact mul_le_mul (mul_le_mul_of_nonneg_left he (norm_nonneg _))
    (norm_sum_dual_powers_le hσ.1.le hy) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans he))

/-- Every finite-frequency integral splits into its evaluated main term and the actual two tails. -/
theorem sum_weightedIntegral_eq_three_terms {σ t y : ℝ} (hσ : σ ∈ Set.Ioo 0 1)
    (x R : ℝ) :
    (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegral ((σ : ℂ) + (t : ℂ) * I) x R (m : ℝ)) =
      (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 (m : ℝ)) -
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegral ((σ : ℂ) + (t : ℂ) * I) 0 x (m : ℝ)) -
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) R (m : ℝ)) := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  exact weightedIntegral_eq_tail_sub_lower_sub_upper hσ hmpos x R

/-- The integral stage of the AFE carries all three explicit errors with the physical cutoffs linked. -/
theorem norm_sum_weightedIntegral_sub_chi_le {σ t x y R t₀ : ℝ}
    (hσ : σ ∈ Set.Ioo 0 1) (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hxhalf : ∃ k : ℤ, x = (k : ℝ) + 1 / 2)
    (hyhalf : ∃ k : ℤ, y = (k : ℝ) + 1 / 2) (hscale : 2 * Real.pi * x * y = |t|)
    (hR : 0 < R) (hcut : ∀ m ∈ Finset.Icc 1 ⌊y⌋₊, t < Real.pi * (m : ℝ) * R)
    (ht₀ : 0 < t₀) (ht : t₀ ≤ |t|) :
    ‖(∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegral ((σ : ℂ) + (t : ℂ) * I) x R (m : ℝ)) -
      chi ((σ : ℂ) + (t : ℂ) * I) *
        ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)‖ ≤
      ‖chi ((σ : ℂ) + (t : ℂ) * I)‖ *
        (Real.exp (-Real.pi * t) / (1 - Real.exp (-Real.pi * t₀))) *
        (y ^ σ * Real.log y + 1) +
      x ^ (-σ) * (Real.log y / Real.pi +
        (Real.eulerMascheroniConstant + 2 * Real.log 2 - 3 / 2) / Real.pi +
          3 / (4 * Real.pi * y) + 3 / (8 * Real.pi * y ^ 2)) +
      2 * R ^ (-σ) / Real.pi * (Real.log y + 1) := by
  rw [sum_weightedIntegral_eq_three_terms hσ x R]
  rw [show
      ((∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 (m : ℝ)) -
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegral ((σ : ℂ) + (t : ℂ) * I) 0 x (m : ℝ)) -
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) R (m : ℝ))) -
        chi ((σ : ℂ) + (t : ℂ) * I) *
          (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1)) =
      ((∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) 0 (m : ℝ)) -
        chi ((σ : ℂ) + (t : ℂ) * I) *
          (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m : ℂ) ^ (((σ : ℂ) + (t : ℂ) * I) - 1))) -
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegral ((σ : ℂ) + (t : ℂ) * I) 0 x (m : ℝ)) -
        (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail ((σ : ℂ) + (t : ℂ) * I) R (m : ℝ)) by ring]
  apply (norm_sub_le _ _).trans
  apply (add_le_add (norm_sub_le (E := ℂ) _ _) (le_refl _)).trans
  exact add_le_add
    (add_le_add (norm_sum_weightedIntegralTail_sub_chi_le hσ hy ht₀ ht)
      (norm_sum_lower_integral_source hσ.2 hx hy hscale hxhalf hyhalf))
    (norm_sum_weightedIntegralTail_le hσ hR hy hcut)

end DhimanKadiriQuesadaHerrera2026
