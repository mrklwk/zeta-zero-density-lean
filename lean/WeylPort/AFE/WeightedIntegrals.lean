module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.FirstDerivativeTest
public import WeylPort.AFE.WeightedIntegralSums

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # The actual weighted oscillatory integrals

Finite integrals use principal complex powers. Integration by parts includes the
zero endpoint whenever the power is locally integrable there. Infinite tails
require a separately proved improper limit and are not totalized set integrals.
-/

namespace DhimanKadiriQuesadaHerrera2026

open Complex MeasureTheory
open scoped ComplexConjugate

/-- The actual integral J(a,b,m), with s and the real frequency kept explicit. -/
noncomputable def weightedIntegral (s : ℂ) (a b m : ℝ) : ℂ :=
  ∫ u in a..b, (u : ℂ) ^ (-s) * exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))

/-- The linear oscillatory factor is continuous everywhere. -/
theorem continuous_linear_wave (m : ℝ) :
    Continuous (fun u : ℝ => exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))) := by
  fun_prop

/-- The exact derivative of the linear oscillatory factor. -/
theorem linear_wave_hasDerivAt (m u : ℝ) :
    HasDerivAt (fun v : ℝ => exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (v : ℂ)))
      ((2 * (Real.pi : ℂ) * I * (m : ℂ)) *
        exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))) u := by
  have hd := ((hasDerivAt_id (u : ℂ)).const_mul (2 * (Real.pi : ℂ) * I * (m : ℂ))).cexp
  simpa only [id_eq, mul_one, mul_comm, one_mul] using hd.comp_ofReal

/-- Every finite J integral is integrable at zero when Re(s)<1. -/
theorem intervalIntegrable_weighted_integrand {s : ℂ} (hs : s.re < 1) (a b m : ℝ) :
    IntervalIntegrable (fun u : ℝ => (u : ℂ) ^ (-s) *
      exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))) volume a b := by
  exact (intervalIntegral.intervalIntegrable_cpow' (show -1 < (-s).re by simp; linarith)).mul_continuousOn
    (continuous_linear_wave m).continuousOn

/-- Integration by parts for a positive-real-part primitive, including the zero endpoint. -/
theorem integral_cpow_linear_wave_parts {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) (m : ℝ) :
    z * (∫ u in 0..x, (u : ℂ) ^ (z - 1) *
      exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))) =
      (x : ℂ) ^ z * exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (x : ℂ)) -
        (2 * (Real.pi : ℂ) * I * (m : ℂ)) *
          (∫ u in 0..x, (u : ℂ) ^ z *
            exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))) := by
  have hzn : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hu := (continuous_ofReal_cpow_const hz).continuousOn (s := Set.uIcc 0 x)
  have hv := (continuous_linear_wave m).continuousOn (s := Set.uIcc 0 x)
  have hdu (u : ℝ) (hu : u ∈ Set.Ioo (min 0 x) (max 0 x)) :
      HasDerivAt (fun v : ℝ => (v : ℂ) ^ z) (z * (u : ℂ) ^ (z - 1)) u := by
    have hup : 0 < u := by simpa only [min_eq_left hx.le] using hu.1
    exact hasDerivAt_ofReal_cpow_const hup.ne' hzn
  have hui : IntervalIntegrable (fun u : ℝ => z * (u : ℂ) ^ (z - 1)) volume 0 x :=
    (intervalIntegral.intervalIntegrable_cpow' (show -1 < (z - 1).re by simp; linarith)).const_mul z
  have hvi : IntervalIntegrable (fun u : ℝ => (2 * (Real.pi : ℂ) * I * (m : ℂ)) *
      exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))) volume 0 x :=
    ((continuous_linear_wave m).const_mul _).intervalIntegrable _ _
  have h := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt hu hv hdu
    (fun u _ => linear_wave_hasDerivAt m u) hui hvi
  rw [intervalIntegral.integral_add (hui.mul_continuousOn hv) (hvi.continuousOn_mul hu)] at h
  simp only [ofReal_zero, zero_cpow hzn, zero_mul, sub_zero] at h
  have he₁ : (∫ u in 0..x, (z * (u : ℂ) ^ (z - 1)) *
      exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))) =
      z * (∫ u in 0..x, (u : ℂ) ^ (z - 1) *
        exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))) := by
    simp_rw [mul_assoc]
    exact intervalIntegral.integral_const_mul _ _
  have he₂ : (∫ u in 0..x, (u : ℂ) ^ z * ((2 * (Real.pi : ℂ) * I * (m : ℂ)) *
      exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ)))) =
      (2 * (Real.pi : ℂ) * I * (m : ℂ)) *
        (∫ u in 0..x, (u : ℂ) ^ z * exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (u : ℂ))) := by
    simp_rw [mul_left_comm ((_) ^ z) (2 * (Real.pi : ℂ) * I * (m : ℂ))]
    exact intervalIntegral.integral_const_mul _ _
  rw [he₁, he₂] at h
  exact eq_sub_iff_add_eq.mpr h

/-- One integration by parts for the actual J integral, with its vanishing lower boundary proved. -/
theorem weightedIntegral_parts {s : ℂ} (hs : s.re < 1) {x : ℝ} (hx : 0 < x) (m : ℝ) :
    (1 - s) * weightedIntegral s 0 x m =
      (x : ℂ) ^ (1 - s) * exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (x : ℂ)) -
        (2 * (Real.pi : ℂ) * I * (m : ℂ)) * weightedIntegral (s - 1) 0 x m := by
  have h := integral_cpow_linear_wave_parts (show 0 < (1 - s).re by simp; linarith) hx m
  simpa only [weightedIntegral, neg_sub, show (1 - s) - 1 = -s by ring] using h

/-- Two integrations by parts give every term of the source J(0,x,m) identity. -/
theorem weightedIntegral_parts_twice {s : ℂ} (hs : s.re < 1) {x : ℝ} (hx : 0 < x) (m : ℝ) :
    weightedIntegral s 0 x m =
      (x : ℂ) ^ (1 - s) * exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (x : ℂ)) / (1 - s) -
        (2 * (Real.pi : ℂ) * I * (m : ℂ)) * (x : ℂ) ^ (2 - s) *
          exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (x : ℂ)) / ((1 - s) * (2 - s)) -
        (4 * (Real.pi : ℂ) ^ 2 * (m : ℂ) ^ 2) / ((1 - s) * (2 - s)) *
          weightedIntegral (s - 2) 0 x m := by
  have h₁ := weightedIntegral_parts hs hx m
  have h₂ := weightedIntegral_parts (s := s - 1) (by simp only [sub_re, one_re]; linarith) hx m
  rw [show 1 - (s - 1) = 2 - s by ring, show s - 1 - 1 = s - 2 by ring] at h₂
  have hn₁ : 1 - s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [sub_re, one_re, zero_re] at hr
    linarith
  have hn₂ : 2 - s ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  let A : ℂ := 2 * (Real.pi : ℂ) * I * (m : ℂ)
  have hprod : (1 - s) * (2 - s) * weightedIntegral s 0 x m =
      (2 - s) * (x : ℂ) ^ (1 - s) * exp (A * (x : ℂ)) -
        A * (x : ℂ) ^ (2 - s) * exp (A * (x : ℂ)) + A ^ 2 * weightedIntegral (s - 2) 0 x m := by
    dsimp only [A]
    linear_combination (2 - s) * h₁ - (2 * (Real.pi : ℂ) * I * (m : ℂ)) * h₂
  have hA : A ^ 2 = -(4 * (Real.pi : ℂ) ^ 2 * (m : ℂ) ^ 2) := by
    dsimp only [A]
    ring_nf
    rw [I_sq]
    ring
  rw [hA] at hprod
  dsimp only [A] at hprod
  field_simp
  linear_combination hprod

/-- The positive-frequency endpoint wave has the exact alternating sign at every half-integer. -/
theorem linear_wave_half_integer (k : ℤ) (m : ℕ) :
    exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (((k : ℝ) + 1 / 2 : ℝ) : ℂ)) =
      (-1 : ℂ) ^ m := by
  have h := congrArg (conj : ℂ → ℂ) (expMode_half_integer k m)
  rw [expMode, ← exp_conj] at h
  simp only [map_mul, conj_I, conj_ofReal, map_pow, map_neg, map_one] at h
  convert h using 1
  congr 1
  push_cast
  ring

/-- The source's two integrations by parts specialize to the actual half-integer endpoint. -/
theorem weightedIntegral_parts_twice_half_integer {s : ℂ} (hs : s.re < 1)
    {x : ℝ} (hx : 0 < x) (k : ℤ) (hxk : x = (k : ℝ) + 1 / 2) (m : ℕ) :
    weightedIntegral s 0 x m =
      (x : ℂ) ^ (1 - s) * (-1 : ℂ) ^ m / (1 - s) -
        (2 * (Real.pi : ℂ) * I * (m : ℂ)) * (x : ℂ) ^ (2 - s) * (-1 : ℂ) ^ m /
          ((1 - s) * (2 - s)) -
        (4 * (Real.pi : ℂ) ^ 2 * (m : ℂ) ^ 2) / ((1 - s) * (2 - s)) *
          weightedIntegral (s - 2) 0 x m := by
  have hw : exp (2 * (Real.pi : ℂ) * I * (m : ℂ) * (x : ℂ)) = (-1 : ℂ) ^ m := by
    rw [hxk]
    exact linear_wave_half_integer k m
  simpa only [Complex.ofReal_natCast, hw] using weightedIntegral_parts_twice hs hx (m : ℝ)

end DhimanKadiriQuesadaHerrera2026
