module
public import GuthMaynard.SecondOrderMeanValue

@[expose] public section

open Complex Finset Set
open scoped BigOperators InnerProductSpace

namespace RiemannZeta.GuthMaynard

/-!
# Weyl differencing for the logarithmic phase

The correlation phase below is the phase produced by one A-process shift.
Its curvature is controlled on a dyadic interval and is fed into the
multi-period B-process from `SecondDerivative.lean`.
-/

/-- Complex-correlation form of finite Weyl differencing. -/
theorem interval_weyl_differencing_complex
    (a : Int -> Complex) (N H : Nat) (C : Real)
    (ha : forall n, n ∈ Finset.Ico (0 : Int) N -> ‖a n‖ <= 1)
    (hC : 0 <= C)
    (hcorr : forall h, h ∈ Finset.range H -> forall k, k ∈ Finset.range H -> h ≠ k ->
      ‖∑ n ∈ Finset.Ico (-(H : Int)) N,
        star (paddedShift a N n h) * paddedShift a N n k‖ <= C) :
    (H : Real) ^ 2 * ‖∑ n ∈ Finset.Ico (0 : Int) N, a n‖ ^ 2 <=
      ((N + H : Nat) : Real) * ((H : Real) * N + (H : Real) ^ 2 * C) := by
  apply interval_weyl_differencing a N H C ha hC
  intro h hh k hk hne
  let z := ∑ n ∈ Finset.Ico (-(H : Int)) N,
    star (paddedShift a N n h) * paddedShift a N n k
  have hre : (∑ n ∈ Finset.Ico (-(H : Int)) N,
      ⟪paddedShift a N n h, paddedShift a N n k⟫_ℝ) = z.re := by
    dsimp only [z]
    simp only [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    simp
    ring
  rw [hre]
  exact (abs_re_le_norm z).trans (hcorr h hh k hk hne)

/-- Difference of two shifted logarithmic phases. -/
noncomputable def logarithmicDifferencePhase
    (t A : Real) (h k : Nat) (x : Real) : Real :=
  logarithmicPhase t (A + x + h) - logarithmicPhase t (A + x + k)

theorem hasDerivAt_logarithmicDifferencePhase
    (t A : Real) (h k : Nat) {x : Real}
    (hh : A + x + h ≠ 0) (hk : A + x + k ≠ 0) :
    HasDerivAt (logarithmicDifferencePhase t A h k)
      (-t / (A + x + h) + t / (A + x + k)) x := by
  have harg (m : Nat) : HasDerivAt (fun y : Real => A + y + m) 1 x := by
    simpa only [Pi.add_apply, id_eq, zero_add] using
      HasDerivAt.add_const (m : Real)
        ((hasDerivAt_const x A).fun_add (hasDerivAt_id x))
  unfold logarithmicDifferencePhase
  convert ((hasDerivAt_logarithmicPhase t hh).comp x (harg h)).fun_sub
    ((hasDerivAt_logarithmicPhase t hk).comp x (harg k)) using 1
  · funext y
    simp only [Function.comp_apply]
  · ring

theorem hasDerivAt_logarithmicDifferencePhase_deriv
    (t A : Real) (h k : Nat) {x : Real}
    (hh : A + x + h ≠ 0) (hk : A + x + k ≠ 0) :
    HasDerivAt (fun y => -t / (A + y + h) + t / (A + y + k))
      (t / (A + x + h) ^ 2 - t / (A + x + k) ^ 2) x := by
  have hleft : HasDerivAt (fun y : Real => -t / (A + y + h))
      (t / (A + x + h) ^ 2) x := by
    have hden : HasDerivAt (fun y : Real => A + y + h) 1 x := by
      simpa only [Pi.add_apply, id_eq, zero_add] using
        HasDerivAt.add_const (h : Real)
          ((hasDerivAt_const x A).fun_add (hasDerivAt_id x))
    convert (hasDerivAt_const x (-t)).div hden hh using 1
    field_simp [hh]
    ring
  have hright : HasDerivAt (fun y : Real => t / (A + y + k))
      (-t / (A + x + k) ^ 2) x := by
    have hden : HasDerivAt (fun y : Real => A + y + k) 1 x := by
      simpa only [Pi.add_apply, id_eq, zero_add] using
        HasDerivAt.add_const (k : Real)
          ((hasDerivAt_const x A).fun_add (hasDerivAt_id x))
    convert (hasDerivAt_const x t).div hden hk using 1
    field_simp [hk]
    ring
  convert hleft.add hright using 1
  ring_nf

/-- A unit discrete second difference of the shifted logarithmic correlation
equals its continuous second derivative at an intermediate point. -/
theorem logarithmicDifferencePhase_secondDifference
    (t A : Real) (h k n : Nat) (hA : 0 < A) :
    exists xi, xi ∈ Set.Ioo (n : Real) (n + 2) ∧
      t / (A + xi + h) ^ 2 - t / (A + xi + k) ^ 2 =
        (logarithmicDifferencePhase t A h k (n + 2) -
          logarithmicDifferencePhase t A h k (n + 1)) -
        (logarithmicDifferencePhase t A h k (n + 1) -
          logarithmicDifferencePhase t A h k n) := by
  let F : Real -> Real := logarithmicDifferencePhase t A h k
  let F' : Real -> Real := fun x => -t / (A + x + h) + t / (A + x + k)
  let F'' : Real -> Real := fun x =>
    t / (A + x + h) ^ 2 - t / (A + x + k) ^ 2
  have hmv := second_order_mean_value F F' F'' n
    (fun x hx => by
      dsimp only [F, F']
      have hx0 : 0 <= x := (Nat.cast_nonneg n).trans hx.1
      exact hasDerivAt_logarithmicDifferencePhase t A h k
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity)))
    (fun x hx => by
      dsimp only [F', F'']
      have hx0 : 0 <= x := (Nat.cast_nonneg n).trans hx.1
      exact hasDerivAt_logarithmicDifferencePhase_deriv t A h k
        (ne_of_gt (by positivity)) (ne_of_gt (by positivity)))
  obtain ⟨xi, hxi, heq⟩ := hmv
  refine ⟨xi, hxi, ?_⟩
  dsimp only [F, F''] at heq
  linarith

theorem logarithmicDifferenceCurvature_bounds
    (t A u v r : Real) (ht : 0 < t) (hA : 0 < A) (hr : 0 < r)
    (huLow : A <= u) (huv : u <= v) (hvHigh : v <= 2 * A)
    (hvu : v - u = r) :
    t * r / (8 * A ^ 3) <= t / u ^ 2 - t / v ^ 2 ∧
      t / u ^ 2 - t / v ^ 2 <= 4 * t * r / A ^ 3 := by
  have hu : 0 < u := hA.trans_le huLow
  have hv : 0 < v := hu.trans_le huv
  have hformula : t / u ^ 2 - t / v ^ 2 =
      t * r * (u + v) / (u ^ 2 * v ^ 2) := by
    field_simp [hu.ne', hv.ne']
    nlinarith
  have huHigh : u <= 2 * A := huv.trans hvHigh
  have hsumLow : 2 * A <= u + v := by linarith
  have hsumHigh : u + v <= 4 * A := by linarith
  have huSqLow : A ^ 2 <= u ^ 2 := by nlinarith
  have hvSqLow : A ^ 2 <= v ^ 2 := by nlinarith
  have huSqHigh : u ^ 2 <= (2 * A) ^ 2 := by nlinarith
  have hvSqHigh : v ^ 2 <= (2 * A) ^ 2 := by nlinarith
  have hdenLow : A ^ 4 <= u ^ 2 * v ^ 2 := by
    calc
      A ^ 4 = A ^ 2 * A ^ 2 := by ring
      _ <= u ^ 2 * v ^ 2 := mul_le_mul huSqLow hvSqLow (sq_nonneg A) (sq_nonneg u)
  have hdenHigh : u ^ 2 * v ^ 2 <= 16 * A ^ 4 := by
    calc
      u ^ 2 * v ^ 2 <= (2 * A) ^ 2 * (2 * A) ^ 2 :=
        mul_le_mul huSqHigh hvSqHigh (sq_nonneg v) (sq_nonneg (2 * A))
      _ = 16 * A ^ 4 := by ring
  rw [hformula]
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 8 * A ^ 3)
      (by positivity : 0 < u ^ 2 * v ^ 2)]
    have hcore : u ^ 2 * v ^ 2 <= 8 * A ^ 3 * (u + v) := by
      calc
        u ^ 2 * v ^ 2 <= 16 * A ^ 4 := hdenHigh
        _ <= 8 * A ^ 3 * (u + v) := by
          have hnonneg := mul_nonneg
            (mul_nonneg (by norm_num : (0 : Real) <= 8) (pow_nonneg hA.le 3))
            (sub_nonneg.mpr hsumLow)
          nlinarith
    calc
      t * r * (u ^ 2 * v ^ 2) <= t * r * (8 * A ^ 3 * (u + v)) :=
        mul_le_mul_of_nonneg_left hcore (mul_pos ht hr).le
      _ = t * r * (u + v) * (8 * A ^ 3) := by ring
  · rw [div_le_div_iff₀ (by positivity : 0 < u ^ 2 * v ^ 2)
      (by positivity : 0 < A ^ 3)]
    have hcore : A ^ 3 * (u + v) <= 4 * (u ^ 2 * v ^ 2) := by
      calc
        A ^ 3 * (u + v) <= A ^ 3 * (4 * A) :=
          mul_le_mul_of_nonneg_left hsumHigh (pow_nonneg hA.le 3)
        _ = 4 * A ^ 4 := by ring
        _ <= 4 * (u ^ 2 * v ^ 2) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcore (mul_pos ht hr).le
    nlinarith

theorem logarithmicDifference_secondDifference_bounds
    (t A : Real) (h k N : Nat) (ht : 0 < t) (hA : 0 < A)
    (hhk : h < k) (hsize : (N + 1 + k : Nat) <= A) :
    forall n, n < N ->
      t * (k - h : Nat) / (8 * A ^ 3) <=
        (logarithmicDifferencePhase t A h k (n + 2) -
          logarithmicDifferencePhase t A h k (n + 1)) -
          (logarithmicDifferencePhase t A h k (n + 1) -
            logarithmicDifferencePhase t A h k n) ∧
      (logarithmicDifferencePhase t A h k (n + 2) -
          logarithmicDifferencePhase t A h k (n + 1)) -
          (logarithmicDifferencePhase t A h k (n + 1) -
            logarithmicDifferencePhase t A h k n) <=
        4 * t * (k - h : Nat) / A ^ 3 := by
  intro n hn
  obtain ⟨xi, hxi, heq⟩ :=
    logarithmicDifferencePhase_secondDifference t A h k n hA
  let u : Real := A + xi + h
  let v : Real := A + xi + k
  have hcastHK : ((k - h : Nat) : Real) = (k : Real) - h := by
    rw [Nat.cast_sub hhk.le]
  have hr : 0 < ((k - h : Nat) : Real) := by exact_mod_cast Nat.sub_pos_of_lt hhk
  have huLow : A <= u := by
    dsimp only [u]
    have hxi0 : 0 <= xi := (Nat.cast_nonneg n).trans hxi.1.le
    have hh0 : (0 : Real) <= h := Nat.cast_nonneg h
    linarith
  have huv : u <= v := by
    dsimp only [u, v]
    have hhkReal : (h : Real) <= k := Nat.cast_le.mpr hhk.le
    linarith
  have hvHigh : v <= 2 * A := by
    dsimp only [v]
    have hnk : (n : Real) + 2 + k <= A := by
      have hnat : n + 2 + k <= N + 1 + k := by omega
      have hcast : ((n + 2 + k : Nat) : Real) <= ((N + 1 + k : Nat) : Real) := by
        exact_mod_cast hnat
      calc
        (n : Real) + 2 + k = ((n + 2 + k : Nat) : Real) := by norm_num
        _ <= ((N + 1 + k : Nat) : Real) := hcast
        _ <= A := hsize
    linarith [hxi.2]
  have hvu : v - u = ((k - h : Nat) : Real) := by
    dsimp only [u, v]
    rw [hcastHK]
    ring
  have hb := logarithmicDifferenceCurvature_bounds t A u v
    ((k - h : Nat) : Real) ht hA hr huLow huv hvHigh hvu
  rw [heq] at hb
  exact hb

/-- B-process estimate for every logarithmic correlation created by one
A-process shift on a dyadic block. -/
theorem logarithmicDifference_B_process
    (t A : Real) (h k N : Nat) (ht : 0 < t) (hA : 0 < A)
    (hhk : h < k) (hsize : ((N + 1 + k : Nat) : Real) <= A) :
    ‖∑ n ∈ Finset.range (N + 1),
        unitaryPhase (logarithmicDifferencePhase t A h k n)‖ <=
      ((N : Real) * (4 * t * (k - h : Nat) / A ^ 3) /
          (2 * Real.pi) + 2) *
        (2 * Real.pi /
            Real.sqrt (t * (k - h : Nat) / (8 * A ^ 3)) +
          2 * (Real.sqrt (t * (k - h : Nat) / (8 * A ^ 3)) /
            (t * (k - h : Nat) / (8 * A ^ 3)) + 1)) := by
  let lambda : Real := t * (k - h : Nat) / (8 * A ^ 3)
  let Lambda : Real := 4 * t * (k - h : Nat) / A ^ 3
  have hr : 0 < ((k - h : Nat) : Real) := by exact_mod_cast Nat.sub_pos_of_lt hhk
  have hlambda : 0 < lambda := by
    dsimp only [lambda]
    positivity
  have hbounds := logarithmicDifference_secondDifference_bounds
    t A h k N ht hA hhk hsize
  simpa only [lambda, Lambda] using
    vanDerCorput_B_process
      (fun n : Nat => logarithmicDifferencePhase t A h k n)
      N lambda Lambda hlambda
        (fun n hn => by
          simpa only [lambda, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
            (hbounds n hn).1)
        (fun n hn => by
          simpa only [Lambda, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
            (hbounds n hn).2)

/-- Integer-indexed logarithmic phase term used by zero-padded shifts. -/
noncomputable def integerLogarithmicTerm (t A : Real) (n : Int) : Complex :=
  unitaryPhase (logarithmicPhase t (A + n))

@[simp] theorem norm_integerLogarithmicTerm (t A : Real) (n : Int) :
    ‖integerLogarithmicTerm t A n‖ = 1 := by
  simp [integerLogarithmicTerm]

theorem padded_logarithmic_correlation_eq (t A : Real) (N H h k : Nat)
    (hh : h < H) (hk : k < H) (hhk : h < k) :
    (∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k) =
      star (∑ m ∈ Finset.range (N - (k - h)),
        unitaryPhase (logarithmicDifferencePhase t A 0 (k - h) m)) := by
  unfold paddedShift
  let s := (Finset.Ico (-(H : Int)) N).filter (fun n =>
    n + (h : Int) ∈ Finset.Ico (0 : Int) N ∧
      n + (k : Int) ∈ Finset.Ico (0 : Int) N)
  have hrestrict :
      (∑ n ∈ Finset.Ico (-(H : Int)) N,
        star (if n + (h : Int) ∈ Finset.Ico (0 : Int) N then
          integerLogarithmicTerm t A (n + h) else 0) *
        (if n + (k : Int) ∈ Finset.Ico (0 : Int) N then
          integerLogarithmicTerm t A (n + k) else 0)) =
      ∑ n ∈ s, star (integerLogarithmicTerm t A (n + h)) *
        integerLogarithmicTerm t A (n + k) := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hhmem : n + (h : Int) ∈ Finset.Ico (0 : Int) N
    · by_cases hkmem : n + (k : Int) ∈ Finset.Ico (0 : Int) N
      · simp [hhmem, hkmem]
      · simp [hhmem, hkmem]
    · simp [hhmem]
  rw [hrestrict]
  have hsum :
      (∑ n ∈ s,
        star (integerLogarithmicTerm t A (n + h)) *
          integerLogarithmicTerm t A (n + k)) =
        ∑ m ∈ Finset.range (N - (k - h)),
          star (integerLogarithmicTerm t A m) *
            integerLogarithmicTerm t A (m + (k - h)) := by
    apply Finset.sum_bij (fun n _hn => Int.toNat (n + h))
    case hi =>
      intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hnh := Finset.mem_Ico.mp hnData.2.1
      have hnk := Finset.mem_Ico.mp hnData.2.2
      apply Finset.mem_range.mpr
      have heq : n + (k : Int) = (n + h) + (k - h : Nat) := by
        omega
      rw [heq] at hnk
      have hcast : Int.toNat (n + h) + (k - h) < N := by
        have hto : ((Int.toNat (n + h) : Nat) : Int) = n + h :=
          Int.toNat_of_nonneg hnh.1
        have hcastInt : ((Int.toNat (n + h) + (k - h) : Nat) : Int) < (N : Int) := by
          push_cast
          rw [hto]
          exact hnk.2
        exact_mod_cast hcastInt
      omega
    case i_inj =>
      intro n₁ hn₁ n₂ hn₂ heq
      have h1 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₁).2.1).1
      have h2 := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn₂).2.1).1
      have heqInt := congrArg (fun m : Nat => (m : Int)) heq
      change ((Int.toNat (n₁ + h) : Nat) : Int) =
        ((Int.toNat (n₂ + h) : Nat) : Int) at heqInt
      rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at heqInt
      omega
    case i_surj =>
      intro m hm
      have hm' := Finset.mem_range.mp hm
      refine ⟨(m : Int) - h, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_Ico.mpr
          constructor
          · have := hh
            omega
          · omega
        · constructor
          · apply Finset.mem_Ico.mpr
            constructor
            · omega
            · have hmk : m + (k - h) < N := by omega
              omega
          · apply Finset.mem_Ico.mpr
            constructor
            · omega
            · have hmk : m + (k - h) < N := by omega
              omega
      · simp
    case h =>
      intro n hn
      have hnonneg := (Finset.mem_Ico.mp (Finset.mem_filter.mp hn).2.1).1
      have hnat : ((Int.toNat (n + h) : Nat) : Int) = n + h := Int.toNat_of_nonneg hnonneg
      congr 2
      · rw [hnat]
      · rw [hnat]
        omega
  rw [hsum]
  change (∑ m ∈ Finset.range (N - (k - h)),
      star (integerLogarithmicTerm t A m) *
        integerLogarithmicTerm t A (m + (k - h))) =
    (starRingEnd Complex) (∑ m ∈ Finset.range (N - (k - h)),
      unitaryPhase (logarithmicDifferencePhase t A 0 (k - h) m))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  change star (integerLogarithmicTerm t A m) *
      integerLogarithmicTerm t A (m + (k - h)) =
    star (unitaryPhase (logarithmicDifferencePhase t A 0 (k - h) m))
  unfold integerLogarithmicTerm logarithmicDifferencePhase
  rw [unitaryPhase_sub]
  simp only [Nat.cast_zero, add_zero]
  rw [star_mul']
  rw [show star ((starRingEnd Complex)
      (unitaryPhase (logarithmicPhase t (A + (m : Real) + (k - h : Nat))))) =
      unitaryPhase (logarithmicPhase t (A + (m : Real) + (k - h : Nat))) by
    change star (star (unitaryPhase
      (logarithmicPhase t (A + (m : Real) + (k - h : Nat))))) = _
    rw [star_star]]
  congr 2
  push_cast
  rw [Nat.cast_sub hhk.le]
  ring_nf

/-- Explicit B-process majorant for a correlation at shift distance `r`. -/
noncomputable def logarithmicCorrelationBound
    (t A : Real) (N r : Nat) : Real :=
  let M := N - r - 1
  ((M : Real) * (4 * t * r / A ^ 3) / (2 * Real.pi) + 2) *
    (2 * Real.pi / Real.sqrt (t * r / (8 * A ^ 3)) +
      2 * (Real.sqrt (t * r / (8 * A ^ 3)) /
        (t * r / (8 * A ^ 3)) + 1))

theorem logarithmicCorrelationBound_nonneg
    (t A : Real) (N r : Nat) (ht : 0 < t) (hA : 0 < A) :
    0 <= logarithmicCorrelationBound t A N r := by
  unfold logarithmicCorrelationBound
  positivity

theorem padded_logarithmic_correlation_norm_le_of_lt
    (t A : Real) (N H h k : Nat) (ht : 0 < t) (hA : 0 < A)
    (hH : H <= N) (hNA : (N : Real) <= A)
    (hh : h < H) (hk : k < H) (hhk : h < k) :
    ‖∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k‖ <=
      logarithmicCorrelationBound t A N (k - h) := by
  have hrpos : 0 < k - h := Nat.sub_pos_of_lt hhk
  have hrN : k - h < N := by omega
  let M := N - (k - h) - 1
  have hlength : M + 1 = N - (k - h) := by
    dsimp only [M]
    omega
  have hsizeNat : M + 1 + (k - h) <= N := by
    dsimp only [M]
    omega
  have hsize : ((M + 1 + (k - h) : Nat) : Real) <= A := by
    exact (Nat.cast_le.mpr hsizeNat).trans hNA
  have hB := logarithmicDifference_B_process t A 0 (k - h) M ht hA
    (by omega) hsize
  rw [padded_logarithmic_correlation_eq t A N H h k hh hk hhk,
    norm_star, ← hlength]
  simpa only [logarithmicCorrelationBound, M, Nat.sub_zero] using hB

/-- Symmetric natural-number distance between two shifts. -/
def shiftDistance (h k : Nat) : Nat := (h - k) + (k - h)

theorem padded_logarithmic_correlation_norm_le
    (t A : Real) (N H h k : Nat) (ht : 0 < t) (hA : 0 < A)
    (hH : H <= N) (hNA : (N : Real) <= A)
    (hh : h < H) (hk : k < H) (hne : h ≠ k) :
    ‖∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k‖ <=
      logarithmicCorrelationBound t A N (shiftDistance h k) := by
  by_cases hhk : h < k
  · have hb := padded_logarithmic_correlation_norm_le_of_lt
      t A N H h k ht hA hH hNA hh hk hhk
    simpa only [shiftDistance, Nat.sub_eq_zero_of_le hhk.le, zero_add] using hb
  · have hkh : k < h := lt_of_le_of_ne (Nat.le_of_not_gt hhk) (Ne.symm hne)
    have hb := padded_logarithmic_correlation_norm_le_of_lt
      t A N H k h ht hA hH hNA hk hh hkh
    let z := ∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n h) *
        paddedShift (integerLogarithmicTerm t A) N n k
    let w := ∑ n ∈ Finset.Ico (-(H : Int)) N,
      star (paddedShift (integerLogarithmicTerm t A) N n k) *
        paddedShift (integerLogarithmicTerm t A) N n h
    have hzw : z = star w := by
      dsimp only [z, w]
      change (∑ n ∈ Finset.Ico (-(H : Int)) N,
        star (paddedShift (integerLogarithmicTerm t A) N n h) *
          paddedShift (integerLogarithmicTerm t A) N n k) =
        (starRingEnd Complex) (∑ n ∈ Finset.Ico (-(H : Int)) N,
          star (paddedShift (integerLogarithmicTerm t A) N n k) *
            paddedShift (integerLogarithmicTerm t A) N n h)
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      change star (paddedShift (integerLogarithmicTerm t A) N n h) *
          paddedShift (integerLogarithmicTerm t A) N n k =
        star (star (paddedShift (integerLogarithmicTerm t A) N n k) *
          paddedShift (integerLogarithmicTerm t A) N n h)
      rw [star_mul']
      rw [star_star]
      ring
    rw [show ‖z‖ = ‖w‖ by rw [hzw, norm_star]]
    simpa only [shiftDistance, Nat.sub_eq_zero_of_le hkh.le, add_zero] using hb

/-- The finite logarithmic A-process with every correlation discharged by
the proved B-process.  The correlation majorant is written as an explicit
finite sum over the possible nonzero shift distances. -/
theorem logarithmic_weyl_AB_process
    (t A : Real) (N H : Nat) (ht : 0 < t) (hA : 0 < A)
    (hH : H <= N) (hNA : (N : Real) <= A) :
    (H : Real) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : Int) N, integerLogarithmicTerm t A n‖ ^ 2 <=
      ((N + H : Nat) : Real) *
        ((H : Real) * N + (H : Real) ^ 2 *
          ∑ r ∈ Finset.Icc 1 (H - 1), logarithmicCorrelationBound t A N r) := by
  let C := ∑ r ∈ Finset.Icc 1 (H - 1), logarithmicCorrelationBound t A N r
  apply interval_weyl_differencing_complex
    (integerLogarithmicTerm t A) N H C
  · intro n _hn
    simp
  · dsimp only [C]
    exact Finset.sum_nonneg fun r _hr => logarithmicCorrelationBound_nonneg t A N r ht hA
  · intro h hh k hk hne
    have hbase := padded_logarithmic_correlation_norm_le
      t A N H h k ht hA hH hNA (Finset.mem_range.mp hh)
        (Finset.mem_range.mp hk) hne
    have hdistPos : 0 < shiftDistance h k := by
      unfold shiftDistance
      omega
    have hdistHigh : shiftDistance h k <= H - 1 := by
      unfold shiftDistance
      by_cases hle : h <= k
      · rw [Nat.sub_eq_zero_of_le hle, zero_add]
        exact (Nat.sub_le k h).trans (Nat.le_sub_one_of_lt (Finset.mem_range.mp hk))
      · have kle : k <= h := Nat.le_of_not_ge hle
        rw [Nat.sub_eq_zero_of_le kle, add_zero]
        exact (Nat.sub_le h k).trans (Nat.le_sub_one_of_lt (Finset.mem_range.mp hh))
    have hmem : shiftDistance h k ∈ Finset.Icc 1 (H - 1) :=
      Finset.mem_Icc.mpr ⟨hdistPos, hdistHigh⟩
    exact hbase.trans (Finset.single_le_sum
      (fun r hr => logarithmicCorrelationBound_nonneg t A N r ht hA) hmem)

/-- Classical A-process shift length `A / t^(1/3)`, truncated to the block
length and rounded down after enforcing one available shift. -/
noncomputable def weylShiftLength (t A : Real) (N : Nat) : Nat :=
  min N (max 1 (Nat.floor (A / t ^ (1 / 3 : Real))))

theorem weylShiftLength_le (t A : Real) (N : Nat) :
    weylShiftLength t A N <= N := by
  exact min_le_left _ _

/-- Explicit squared majorant produced by the optimized A-after-B process. -/
noncomputable def logarithmicWeylMajorant (t A : Real) (N : Nat) : Real :=
  let H := weylShiftLength t A N
  ((N + H : Nat) : Real) *
    ((H : Real) * N + (H : Real) ^ 2 *
      ∑ r ∈ Finset.Icc 1 (H - 1), logarithmicCorrelationBound t A N r)

/-- Explicit norm majorant for an optimized logarithmic Weyl block. -/
noncomputable def logarithmicWeylBound (t A : Real) (N : Nat) : Real :=
  Real.sqrt (logarithmicWeylMajorant t A N) / weylShiftLength t A N

theorem integerLogarithmicSum_eq (t : Real) (A N : Nat) :
    (∑ n ∈ Finset.Ico (0 : Int) N, integerLogarithmicTerm t A n) =
      logarithmicSum t A (A + N) := by
  unfold logarithmicSum phaseSum
  apply Finset.sum_bij (fun n _hn => A + Int.toNat n)
  case hi =>
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    apply Finset.mem_Ico.mpr
    constructor
    · omega
    · have hcast : Int.toNat n < N := by
        have hto : ((Int.toNat n : Nat) : Int) = n := Int.toNat_of_nonneg hn'.1
        have : ((Int.toNat n : Nat) : Int) < (N : Int) := by rw [hto]; exact hn'.2
        exact_mod_cast this
      omega
  case i_inj =>
    intro n₁ hn₁ n₂ hn₂ heq
    have h1 := (Finset.mem_Ico.mp hn₁).1
    have h2 := (Finset.mem_Ico.mp hn₂).1
    have hnat : Int.toNat n₁ = Int.toNat n₂ := by omega
    have hcast := congrArg (fun m : Nat => (m : Int)) hnat
    change ((Int.toNat n₁ : Nat) : Int) = ((Int.toNat n₂ : Nat) : Int) at hcast
    rw [Int.toNat_of_nonneg h1, Int.toNat_of_nonneg h2] at hcast
    exact hcast
  case i_surj =>
    intro m hm
    have hm' := Finset.mem_Ico.mp hm
    refine ⟨(m - A : Nat), ?_, by omega⟩
    apply Finset.mem_Ico.mpr
    constructor
    · positivity
    · exact_mod_cast (show m - A < N by omega)
  case h =>
    intro n hn
    have hn0 := (Finset.mem_Ico.mp hn).1
    unfold integerLogarithmicTerm
    congr 3
    have hto : ((Int.toNat n : Nat) : Int) = n := Int.toNat_of_nonneg hn0
    have htoReal : ((Int.toNat n : Nat) : Real) = (n : Real) := by
      exact_mod_cast hto
    push_cast
    rw [htoReal]

/-- Finite optimized Weyl bound for a logarithmic block.  The shift length
is the classical `A / t^(1/3)` choice; every term on the right is an explicit
closed finite expression, with no analytic premise. -/
theorem logarithmic_weyl_optimized
    (t : Real) (A N : Nat) (ht : 0 < t) (hA : 0 < A) (hNA : N <= A) :
    let H := weylShiftLength t A N
    (H : Real) ^ 2 * ‖logarithmicSum t A (A + N)‖ ^ 2 <=
      ((N + H : Nat) : Real) *
        ((H : Real) * N + (H : Real) ^ 2 *
          ∑ r ∈ Finset.Icc 1 (H - 1), logarithmicCorrelationBound t A N r) := by
  dsimp only
  rw [← integerLogarithmicSum_eq]
  exact logarithmic_weyl_AB_process t A N (weylShiftLength t A N) ht
    (by positivity) (weylShiftLength_le t A N) (by exact_mod_cast hNA)

/-- Norm form of the optimized logarithmic Weyl estimate. -/
theorem norm_logarithmicSum_le_weylBound
    (t : Real) (A N : Nat) (ht : 0 < t) (hA : 0 < A) (hN : 0 < N)
    (hNA : N <= A) :
    ‖logarithmicSum t A (A + N)‖ <= logarithmicWeylBound t A N := by
  let H := weylShiftLength t A N
  have hH : 0 < H := by
    dsimp only [H, weylShiftLength]
    apply lt_min hN
    exact lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  have hsquared := logarithmic_weyl_optimized t A N ht hA hNA
  dsimp only at hsquared
  have hsq : ((H : Real) * ‖logarithmicSum t A (A + N)‖) ^ 2 <=
      logarithmicWeylMajorant t A N := by
    dsimp only [logarithmicWeylMajorant, H]
    nlinarith
  have hsqrt : (H : Real) * ‖logarithmicSum t A (A + N)‖ <=
      Real.sqrt (logarithmicWeylMajorant t A N) :=
    Real.le_sqrt_of_sq_le hsq
  unfold logarithmicWeylBound
  rw [le_div_iff₀ (Nat.cast_pos.mpr hH)]
  simpa only [mul_comm] using hsqrt

end RiemannZeta.GuthMaynard
