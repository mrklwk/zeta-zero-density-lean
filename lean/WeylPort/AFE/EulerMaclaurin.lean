module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.PoissonFourier
public import WeylPort.Analytic.EulerMaclaurin
public import Mathlib.Analysis.Calculus.Deriv.Shift

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # Euler–Maclaurin for the source's full real-endpoint domain

This module reuses the existing pinned PNT+ Euler–Maclaurin theorem and proves
the integer translation and endpoint bridges needed for arbitrary real a ≤ b.
-/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory

/-- The pinned upstream Bernoulli function agrees with the periodic sawtooth on its domain. -/
theorem B1_eq_fract {x : ℝ} (hx : 0 ≤ x) : B1 x = Int.fract x - 1 / 2 := by
  unfold B1 Int.fract
  rw [← Int.cast_natCast ⌊x⌋₊, Int.natCast_floor_eq_floor hx]

/-- An integer shift converts the natural-floor sum to the source's integer-floor sum. -/
theorem sum_shift_nat_floor (F : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b)
    (k : ℤ) (hk : (k : ℝ) ≤ a) :
    (∑ n ∈ Finset.Ioc ⌊a - k⌋₊ ⌊b - k⌋₊, F ((n : ℝ) + k)) =
      ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F (n : ℝ) := by
  have hfloor (x : ℝ) (hx : (k : ℝ) ≤ x) :
      (⌊x - k⌋₊ : ℤ) = ⌊x⌋ - k := by
    rw [Int.natCast_floor_eq_floor (sub_nonneg.mpr hx), Int.floor_sub_intCast]
  have hfa := hfloor a hk
  have hfb := hfloor b (hk.trans hab)
  apply Finset.sum_bij (fun (n : ℕ) _ => (n : ℤ) + k)
  · intro n hn
    simp only [Finset.mem_Ioc] at hn ⊢
    have hna : (⌊a - k⌋₊ : ℤ) < n := by exact_mod_cast hn.1
    have hnb : (n : ℤ) ≤ ⌊b - k⌋₊ := by exact_mod_cast hn.2
    omega
  · intro n _ m _ hnm
    exact_mod_cast (add_right_cancel hnm : (n : ℤ) = m)
  · intro m hm
    simp only [Finset.mem_Ioc] at hm
    have hka : k ≤ ⌊a⌋ := Int.le_floor.mpr hk
    have hmk : 0 ≤ m - k := by omega
    refine ⟨(m - k).toNat, ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      constructor
      · have ht : (⌊a - k⌋₊ : ℤ) < ((m - k).toNat : ℤ) := by
          rw [Int.toNat_of_nonneg hmk]
          omega
        exact_mod_cast ht
      · have ht : ((m - k).toNat : ℤ) ≤ ⌊b - k⌋₊ := by
          rw [Int.toNat_of_nonneg hmk]
          omega
        exact_mod_cast ht
    · rw [Int.toNat_of_nonneg hmk]
      omega
  · intro n _
    simp only [Int.cast_add, Int.cast_natCast]

/-- Exact first-order Euler–Maclaurin with arbitrary real endpoints and the source's (a,b] sum. -/
theorem euler_maclaurin_int {a b : ℝ} (hab : a ≤ b) (F : ℝ → ℂ)
    (hd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ F x)
    (hc : ContinuousOn (deriv F) (Set.Icc a b)) :
    (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, F (n : ℝ)) =
      F a * ((Int.fract a - 1 / 2 : ℝ) : ℂ) - F b * ((Int.fract b - 1 / 2 : ℝ) : ℂ) +
        (∫ x in a..b, F x) + ∫ x in a..b, deriv F x * ((Int.fract x - 1 / 2 : ℝ) : ℂ) := by
  let k : ℤ := ⌊a⌋
  have hk : (k : ℝ) ≤ a := Int.floor_le a
  have ha0 : 0 ≤ a - k := sub_nonneg.mpr hk
  have hab' : a - k ≤ b - k := sub_le_sub_right hab _
  have hm : Set.MapsTo (fun x : ℝ => x + k) (Set.Icc (a - k) (b - k)) (Set.Icc a b) := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have hd' (x : ℝ) (hx : x ∈ Set.Icc (a - k) (b - k)) :
      DifferentiableAt ℝ (fun u => F (u + k)) x :=
    (hd _ (hm hx)).comp x (differentiableAt_id.add_const _)
  have hc' : ContinuousOn (deriv (fun u => F (u + k))) (Set.uIcc (a - k) (b - k)) := by
    rw [Set.uIcc_of_le hab']
    have heq : deriv (fun u => F (u + k)) = fun u => deriv F (u + k) :=
      funext (fun u => deriv_comp_add_const F (k : ℝ) u)
    rw [heq]
    exact hc.comp (continuousOn_id.add continuousOn_const) hm
  have he := sum_eq_integral_add_integral_deriv ha0 hab' hd' hc'
  rw [sum_shift_nat_floor F hab k hk] at he
  simp only [sub_add_cancel] at he
  rw [B1_eq_fract ha0, B1_eq_fract (ha0.trans hab'), Int.fract_sub_intCast,
    Int.fract_sub_intCast] at he
  rw [intervalIntegral.integral_comp_add_right] at he
  simp only [sub_add_cancel] at he
  have hi : (∫ x in (a - k)..(b - k), deriv (fun u => F (u + k)) x * (B1 x : ℂ)) =
      ∫ x in a..b, deriv F x * ((Int.fract x - 1 / 2 : ℝ) : ℂ) := by
    calc
      _ = ∫ x in (a - k)..(b - k),
          deriv F (x + k) * ((Int.fract (x + k) - 1 / 2 : ℝ) : ℂ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hab'] at hx
        dsimp only
        rw [deriv_comp_add_const, B1_eq_fract (ha0.trans hx.1), Int.fract_add_intCast]
      _ = _ := by
        simpa only [sub_add_cancel] using
          intervalIntegral.integral_comp_add_right
            (fun x => deriv F x * ((Int.fract x - 1 / 2 : ℝ) : ℂ)) (k : ℝ)
            (a := a - k) (b := b - k)
  refine he.trans ?_
  congr 1


/-- The literal complex boundary term; its norm is the source's G(a,b). -/
noncomputable def poissonBoundary (f g : ℝ → ℝ) (a b : ℝ) : ℂ :=
  weightedWave f g a * ((Int.fract a - 1 / 2 : ℝ) : ℂ) -
    weightedWave f g b * ((Int.fract b - 1 / 2 : ℝ) : ℂ)

/-- The actual (a,b] weighted sum has the source's two Fourier series and complex boundary. -/
theorem weighted_sum_eq_fourier {f g : ℝ → ℝ} {a b : ℝ}
    (h : PartIRegularity f g a b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) =
      poissonBoundary f g a b + (∫ x in a..b, weightedWave f g x) +
        ((∑' n, negativeCoefficient f g a b n) - ∑' n, positiveCoefficient f g a b n) := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) :
      DifferentiableAt ℝ (weightedWave f g) x :=
    (weighted_wave_hasDerivAt (h.f_differentiable x hx) (h.g_differentiable x hx)).differentiableAt
  have heq (x : ℝ) (hx : x ∈ Set.Icc a b) :
      waveDerivative f g x = deriv (weightedWave f g) x :=
    waveDerivative_eq_deriv (h.f_differentiable x hx) (h.g_differentiable x hx)
  have hc : ContinuousOn (deriv (weightedWave f g)) (Set.Icc a b) :=
    h.waveDerivative_continuous.congr (fun x hx => (heq x hx).symm)
  have he := euler_maclaurin_int h.lt.le (weightedWave f g) hd hc
  have hi : (∫ x in a..b, deriv (weightedWave f g) x * ((Int.fract x - 1 / 2 : ℝ) : ℂ)) =
      ∫ x in a..b, waveDerivative f g x * ((Int.fract x - 1 / 2 : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le h.lt.le] at hx
    dsimp only
    rw [heq x hx]
  rw [hi, integral_waveDerivative_sawtooth h] at he
  exact he

/-- The actual source wave has norm g(x) for a nonnegative weight. -/
theorem norm_weightedWave {f g : ℝ → ℝ} {x : ℝ} (hg : 0 ≤ g x) :
    ‖weightedWave f g x‖ = g x := by
  unfold weightedWave
  have he : ‖Complex.exp (2 * Real.pi * Complex.I * (f x : ℂ))‖ = 1 := by
    have hp : 2 * (Real.pi : ℂ) * Complex.I * (f x : ℂ) =
        (((2 * Real.pi * f x : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [hp, Complex.norm_exp_ofReal_mul_I]
  rw [norm_mul, he, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg]

/-- The periodic sawtooth has the source's sharp endpoint bound one half. -/
theorem abs_fract_sub_half_le (x : ℝ) : |Int.fract x - 1 / 2| ≤ 1 / 2 := by
  apply abs_le.mpr
  constructor <;> linarith [Int.fract_nonneg x, Int.fract_lt_one x]

/-- The actual complex boundary has the printed general-endpoint bound. -/
theorem norm_poissonBoundary_le {f g : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ g a) (hb : 0 ≤ g b) :
    ‖poissonBoundary f g a b‖ ≤ (g a + g b) / 2 := by
  have ht := norm_sub_le
    (weightedWave f g a * ((Int.fract a - 1 / 2 : ℝ) : ℂ))
    (weightedWave f g b * ((Int.fract b - 1 / 2 : ℝ) : ℂ))
  simp only [norm_mul, norm_weightedWave ha, norm_weightedWave hb,
    Complex.norm_real, Real.norm_eq_abs] at ht
  have h1 := mul_le_mul_of_nonneg_left (abs_fract_sub_half_le a) ha
  have h2 := mul_le_mul_of_nonneg_left (abs_fract_sub_half_le b) hb
  exact ht.trans (by linarith)

/-- The literal complex boundary vanishes at both half-integer endpoints. -/
theorem poissonBoundary_half_integer (f g : ℝ → ℝ) (k l : ℤ) :
    poissonBoundary f g ((k : ℝ) + 1 / 2) ((l : ℝ) + 1 / 2) = 0 := by
  have hfract (j : ℤ) : Int.fract ((j : ℝ) + 1 / 2) = (1 / 2 : ℝ) := by
    rw [Int.fract_intCast_add]
    exact Int.fract_eq_self.mpr (by norm_num)
  rw [poissonBoundary, hfract, hfract]
  simp only [sub_self, Complex.ofReal_zero, mul_zero]

end DhimanKadiriQuesadaHerrera2026
