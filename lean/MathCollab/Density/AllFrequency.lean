module
public import MathCollab.Density.Oscillatory

@[expose] public section

open Complex MeasureTheory Real Set

namespace MathCollab.Density

/-- Additivity on positive adjacent intervals. -/
theorem gmReflectionIntegral_add {tau a b c : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    gmReflectionIntegral tau a b + gmReflectionIntegral tau b c =
      gmReflectionIntegral tau a c := by
  exact intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_gmReflectionIntegrand hab ha)
    (intervalIntegrable_gmReflectionIntegrand hbc (ha.trans_le hab))

/-- Uniform bound for every real frequency, with no hypothesis on its sign. -/
theorem norm_gmReflectionIntegral_le_six_div_sqrt {tau a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ‖gmReflectionIntegral tau a b‖ ≤ 6 / Real.sqrt (2 * Real.pi * a) := by
  let s := Real.sqrt (2 * Real.pi * a)
  let L := (tau - s) / (2 * Real.pi)
  let R := (tau + s) / (2 * Real.pi)
  have hc : 0 < 2 * Real.pi := by positivity
  have hs : 0 < s := Real.sqrt_pos.2 (mul_pos hc ha)
  have hs2 : s ^ 2 = 2 * Real.pi * a := Real.sq_sqrt (mul_pos hc ha).le
  have hL : 2 * Real.pi * L = tau - s := by
    dsimp [L]; field_simp
  have hR : 2 * Real.pi * R = tau + s := by
    dsimp [R]; field_simp
  have hLR : L ≤ R := by nlinarith
  have h26 : 2 / s ≤ 6 / s := div_le_div_of_nonneg_right (by norm_num) hs.le
  by_cases hbL : b ≤ L
  · have hgap : s ≤ tau - 2 * Real.pi * b := by nlinarith
    exact (norm_gmReflectionIntegral_le_left hab ha (by linarith)).trans
      ((div_le_div_of_nonneg_left (by norm_num) hs hgap).trans h26)
  by_cases hRa : R ≤ a
  · have hgap : s ≤ 2 * Real.pi * a - tau := by nlinarith
    exact (norm_gmReflectionIntegral_le_right hab ha (by linarith)).trans
      ((div_le_div_of_nonneg_left (by norm_num) hs hgap).trans h26)
  have hLb : L ≤ b := le_of_lt (lt_of_not_ge hbL)
  have haR : a ≤ R := le_of_lt (lt_of_not_ge hRa)
  let u := max a L
  let v := min b R
  have hau : a ≤ u := le_max_left _ _
  have huL : L ≤ u := le_max_right _ _
  have hvb : v ≤ b := min_le_left _ _
  have hvR : v ≤ R := min_le_right _ _
  have huv : u ≤ v := max_le (le_min hab haR) (le_min hLb hLR)
  have hu : 0 < u := ha.trans_le hau
  have hv : 0 < v := hu.trans_le huv
  have hleft : ‖gmReflectionIntegral tau a u‖ ≤ 2 / s := by
    by_cases hLa : L ≤ a
    · have hua : u = a := max_eq_left hLa
      simp only [hua, gmReflectionIntegral, intervalIntegral.integral_same, norm_zero]
      positivity
    · have huL' : u = L := max_eq_right (le_of_lt (lt_of_not_ge hLa))
      have hgap : tau - 2 * Real.pi * u = s := by rw [huL']; linarith
      have ht : 2 * Real.pi * u < tau := by linarith
      simpa only [hgap] using norm_gmReflectionIntegral_le_left hau ha ht
  have hright : ‖gmReflectionIntegral tau v b‖ ≤ 2 / s := by
    by_cases hbR : b ≤ R
    · have hvb' : v = b := min_eq_left hbR
      simp only [hvb', gmReflectionIntegral, intervalIntegral.integral_same, norm_zero]
      positivity
    · have hvR' : v = R := min_eq_right (le_of_lt (lt_of_not_ge hbR))
      have hgap : 2 * Real.pi * v - tau = s := by rw [hvR']; linarith
      have ht : tau < 2 * Real.pi * v := by linarith
      simpa only [hgap] using norm_gmReflectionIntegral_le_right hvb hv ht
  have hwidth : (R - L) / a = 2 / s := by
    apply (div_eq_div_iff ha.ne' hs.ne').2
    have hspan : (2 * Real.pi) * (R - L) = 2 * s := by linarith
    nlinarith [sq_nonneg (s - 1)]
  have hmiddle : ‖gmReflectionIntegral tau u v‖ ≤ 2 / s := by
    calc
      ‖gmReflectionIntegral tau u v‖ ≤ (v - u) / a :=
        norm_gmReflectionIntegral_le_length_div huv ha hau
      _ ≤ (R - L) / a := div_le_div_of_nonneg_right (by linarith) ha.le
      _ = 2 / s := hwidth
  have hsplit : gmReflectionIntegral tau a b =
      (gmReflectionIntegral tau a u + gmReflectionIntegral tau u v) +
        gmReflectionIntegral tau v b := by
    rw [gmReflectionIntegral_add ha hau huv,
      gmReflectionIntegral_add ha (hau.trans huv) hvb]
  change ‖gmReflectionIntegral tau a b‖ ≤ 6 / s
  rw [hsplit]
  calc
    ‖(gmReflectionIntegral tau a u + gmReflectionIntegral tau u v) +
        gmReflectionIntegral tau v b‖ ≤
      (‖gmReflectionIntegral tau a u‖ + ‖gmReflectionIntegral tau u v‖) +
        ‖gmReflectionIntegral tau v b‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (2 / s + 2 / s) + 2 / s := add_le_add (add_le_add hleft hmiddle) hright
    _ = 6 / s := by ring

/-- Oscillatory integral bound in phase notation. -/
theorem norm_oscillatoryIntegral_le {a b tau : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖∫ z in a..b, (z : ℂ)⁻¹ *
      Complex.exp (I * ((tau * Real.log z - 2 * Real.pi * z : ℝ) : ℂ))‖ ≤
        6 / Real.sqrt (2 * Real.pi * a) := by
  simpa only [gmReflectionIntegral, mul_comm I] using
    norm_gmReflectionIntegral_le_six_div_sqrt (tau := tau) ha hab

end MathCollab.Density
