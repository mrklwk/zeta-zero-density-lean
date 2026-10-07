module
public import WeylPort.AFE.SecondCoeffBounds
public import WeylPort.AFE.UniformElementary

@[expose] public section

namespace WeylPort
open DhimanKadiriQuesadaHerrera2026

/-- Coarse positive-frequency coefficients suffice for a bounded AFE error. -/
theorem plus_coefficients_uniform {y : ℝ} (hy : 1 ≤ y) :
    plusSquareBound y ≤ 2/y ∧ plusCubeBound y ≤ 2/y := by
  have hy0 : 0 < y := by linarith
  have hl : Real.log (y+1) ≤ y := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < y+1)
    linarith
  have hg : Real.eulerMascheroniConstant ≤ 1 :=
    Real.eulerMascheroniConstant_lt_two_thirds.le.trans (by norm_num)
  have hnum : Real.log (y+1) + Real.eulerMascheroniConstant ≤ 2*y := by linarith
  have hs : y ≤ y^2 := by nlinarith
  have hc : y^2 ≤ y^3 := by nlinarith [sq_nonneg (y-1)]
  constructor
  · unfold plusSquareBound
    apply (sub_le_self _ (by positivity)).trans
    apply (div_le_div_of_nonneg_right hnum (by positivity)).trans
    apply (div_le_iff₀ (by positivity : 0 < y^2)).mpr
    field_simp
    nlinarith
  · unfold plusCubeBound
    apply (sub_le_self _ (by positivity)).trans
    apply (div_le_div_of_nonneg_right hnum (by positivity)).trans
    apply (div_le_iff₀ (by positivity : 0 < y^3)).mpr
    field_simp
    nlinarith

/-- Coarse upper-frequency coefficients use the actual displayed digamma expressions. -/
theorem minus_coefficients_uniform {M : ℕ} {y : ℝ} (hy : 1 ≤ y)
    (hlo : 1/2 ≤ (M:ℝ)+1-y) (hhi : (M:ℝ)+1-y ≤ 1) :
    minusSquareBound M y ≤ 7/y ∧ minusCubeBound M y ≤ 15/y := by
  let δ := (M:ℝ)+1-y
  have hd0 : 0 < δ := by dsimp [δ]; linarith
  have hy0 : 0 < y := by linarith
  have hδ : 1/2 ≤ δ := hlo
  have hδ1 : δ ≤ 1 := hhi
  have hd1 : 1 ≤ δ+1 := by linarith
  have hψ := digamma_gap_bounds hlo hhi
  change -4 ≤ (Complex.digamma (δ:ℂ)).re ∧ (Complex.digamma (δ:ℂ)).re ≤ 0 at hψ
  have hMs : 1 ≤ (M:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) M]
  have hM0 : 0 < (M:ℝ)+1 := by positivity
  have hlog0 : 0 ≤ Real.log ((M:ℝ)+1) := Real.log_nonneg hMs
  have hlog : Real.log ((M:ℝ)+1) ≤ y := by
    have := Real.log_le_sub_one_of_pos hM0
    dsimp [δ] at hδ1
    linarith
  have hiM : 1/((M:ℝ)+1) ≤ 1 := (div_le_one hM0).mpr hMs
  have hiδ2 : 1/δ^2 ≤ 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hd0)).mpr
    nlinarith
  have hiδ3 : 1/δ^3 ≤ 8 := by
    apply (div_le_iff₀ (pow_pos hd0 3)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδ (sq_nonneg δ), sq_nonneg (δ-1/2)]
  have hiδp : 1/(δ+1) ≤ 1 := (div_le_one (by positivity)).mpr hd1
  have hiδp2 : 1/(δ+1)^2 ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have hiδp3 : 1/(δ+1)^3 ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg δ])
  have hiδhalf : 1/(2*(δ+1)^2) ≤ 1 := (div_le_one (by positivity)).mpr (by nlinarith)
  have hsq : y ≤ y^2 := by nlinarith
  have hcu : y^2 ≤ y^3 := by nlinarith [sq_nonneg (y-1)]
  constructor
  · change (1/δ^2 + 1/(δ+1)^2 + 1/(δ+1))/y -
      (Real.log ((M:ℝ)+1) - 1/((M:ℝ)+1) - (Complex.digamma (δ:ℂ)).re)/y^2 ≤ 7/y
    have ha : (1/δ^2 + 1/(δ+1)^2 + 1/(δ+1))/y ≤ 6/y := by gcongr; linarith
    have hb : -(Real.log ((M:ℝ)+1) - 1/((M:ℝ)+1) - (Complex.digamma (δ:ℂ)).re)/y^2 ≤ 1/y := by
      apply (div_le_div_of_nonneg_right (show -(Real.log ((M:ℝ)+1) - 1/((M:ℝ)+1) - (Complex.digamma (δ:ℂ)).re) ≤ 1 by linarith [hψ.2]) (by positivity)).trans
      exact one_div_le_one_div_of_le hy0 hsq
    rw [neg_div] at hb
    simp only [div_eq_mul_inv] at ha hb ⊢
    linarith
  · change (1/δ^3 + 1/(δ+1)^3 + 1/(2*(δ+1)^2))/y -
      (1/δ^2 + 1/(δ+1))/y^2 +
      (Real.log ((M:ℝ)+1) - 1/(2*((M:ℝ)+1)) - (Complex.digamma (δ:ℂ)).re)/y^3 ≤ 15/y
    have ha : (1/δ^3 + 1/(δ+1)^3 + 1/(2*(δ+1)^2))/y ≤ 10/y := by gcongr; linarith
    have hb : 0 ≤ (1/δ^2 + 1/(δ+1))/y^2 := by positivity
    have hc : (Real.log ((M:ℝ)+1) - 1/(2*((M:ℝ)+1)) - (Complex.digamma (δ:ℂ)).re)/y^3 ≤ 5/y := by
      apply (div_le_div_of_nonneg_right (show Real.log ((M:ℝ)+1) - 1/(2*((M:ℝ)+1)) - (Complex.digamma (δ:ℂ)).re ≤ y+4 by linarith [hψ.1, show 0 ≤ 1/(2*((M:ℝ)+1)) by positivity]) (by positivity)).trans
      apply (div_le_iff₀ (pow_pos hy0 3)).mpr
      field_simp
      nlinarith
    simp only [div_eq_mul_inv] at ha hb hc ⊢
    linarith

end WeylPort
