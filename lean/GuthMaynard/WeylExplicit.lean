module
public import GuthMaynard.Weyl
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open Complex Finset Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Explicit Weyl exponent bounds

This module simplifies the finite A-after-B estimate to the classical
`(1/6, 2/3)` exponent scale on medium logarithmic blocks.  All constants and
shift choices are explicit and the final prefix estimate has no analytic
premise.
-/

theorem vdc_product_bound
    (n x : Real) (hn : 0 <= n) (hx : 0 < x) (hx1 : x <= 1) :
    (n * (32 * x) / (2 * Real.pi) + 2) *
        (2 * Real.pi / Real.sqrt x + 2 * (Real.sqrt x / x + 1)) <=
      100 * (n * Real.sqrt x + 1 / Real.sqrt x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs_sq : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  have hxy : Real.sqrt x / x = 1 / Real.sqrt x := by
    rw [div_eq_iff hx.ne', one_div]
    field_simp [hs.ne']
    nlinarith
  have hxs : x <= Real.sqrt x := by
    have hs1 : Real.sqrt x <= 1 := (Real.sqrt_le_iff).2 ⟨by norm_num, by simpa using hx1⟩
    calc
      x = Real.sqrt x * Real.sqrt x := by nlinarith
      _ <= Real.sqrt x * 1 := mul_le_mul_of_nonneg_left hs1 hs.le
      _ = Real.sqrt x := mul_one _
  have hone : 1 <= 1 / Real.sqrt x := by
    rw [le_div_iff₀ hs]
    have hs1 : Real.sqrt x <= 1 := by nlinarith [Real.sqrt_nonneg x]
    simpa using hs1
  have hpi3 : (3 : Real) < Real.pi := Real.pi_gt_three
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hinvpi : 32 / Real.pi <= (11 : Real) := by
    rw [div_le_iff₀ (by positivity : 0 < Real.pi)]
    nlinarith
  rw [hxy]
  have heq :
      (n * (32 * x) / (2 * Real.pi) + 2) *
          (2 * Real.pi / Real.sqrt x + 2 * (1 / Real.sqrt x + 1)) =
        32 * n * (x / Real.sqrt x) +
        32 * n * (x / (Real.pi * Real.sqrt x)) +
        32 * n * (x / Real.pi) +
        4 * Real.pi / Real.sqrt x + 4 / Real.sqrt x + 4 := by
    field_simp [Real.pi_ne_zero, hs.ne']
    ring
  rw [heq]
  have hxdiv : x / Real.sqrt x = Real.sqrt x := by
    rw [div_eq_iff hs.ne']
    nlinarith
  have hterm2 : 32 * n * (x / (Real.pi * Real.sqrt x)) <=
      11 * n * Real.sqrt x := by
    rw [show x / (Real.pi * Real.sqrt x) = Real.sqrt x / Real.pi by
      field_simp [Real.pi_ne_zero, hs.ne']; nlinarith]
    calc
      32 * n * (Real.sqrt x / Real.pi) =
          (32 / Real.pi) * (n * Real.sqrt x) := by ring
      _ <= 11 * (n * Real.sqrt x) :=
        mul_le_mul_of_nonneg_right hinvpi (mul_nonneg hn hs.le)
      _ = 11 * n * Real.sqrt x := by ring
  have hterm3 : 32 * n * (x / Real.pi) <= 11 * n * Real.sqrt x := by
    calc
      32 * n * (x / Real.pi) = (32 / Real.pi) * (n * x) := by ring
      _ <= 11 * (n * x) :=
        mul_le_mul_of_nonneg_right hinvpi (mul_nonneg hn hx.le)
      _ <= 11 * (n * Real.sqrt x) := by gcongr
      _ = 11 * n * Real.sqrt x := by ring
  have hterm4 : 4 * Real.pi / Real.sqrt x <= 16 / Real.sqrt x := by
    exact (div_le_div_iff_of_pos_right hs).2 (by nlinarith)
  have hfour : (4 : Real) <= 4 / Real.sqrt x := by
    calc
      (4 : Real) = 4 * 1 := by ring
      _ <= 4 * (1 / Real.sqrt x) := mul_le_mul_of_nonneg_left hone (by norm_num)
      _ = 4 / Real.sqrt x := by ring
  rw [hxdiv]
  have hns : 0 <= n * Real.sqrt x := mul_nonneg hn hs.le
  have hinvs : 0 <= 1 / Real.sqrt x := by positivity
  simp only [div_eq_mul_inv, one_mul] at hterm2 hterm3 hterm4 hfour hinvs ⊢
  ring_nf at hterm2 hterm3 hterm4 hfour hns hinvs ⊢
  linarith

theorem logarithmicCorrelationBound_le_simple
    (t A : Real) (N r : Nat) (ht : 0 < t) (hA : 0 < A)
    (hr : 0 < r) (hsmall : t * r / (8 * A ^ 3) <= 1) :
    logarithmicCorrelationBound t A N r <=
      100 * ((N : Real) * Real.sqrt (t * r / (8 * A ^ 3)) +
        1 / Real.sqrt (t * r / (8 * A ^ 3))) := by
  let x : Real := t * r / (8 * A ^ 3)
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hx1 : x <= 1 := hsmall
  have hMN : ((N - r - 1 : Nat) : Real) <= N := by exact_mod_cast Nat.sub_le N (r + 1)
  have hsecond : 0 <=
      2 * Real.pi / Real.sqrt x + 2 * (Real.sqrt x / x + 1) := by positivity
  have hfirst :
      ((N - r - 1 : Nat) : Real) * (32 * x) / (2 * Real.pi) + 2 <=
        (N : Real) * (32 * x) / (2 * Real.pi) + 2 := by gcongr
  have hraw := mul_le_mul_of_nonneg_right hfirst hsecond
  have hproduct := vdc_product_bound (N : Real) x (Nat.cast_nonneg N) hx hx1
  unfold logarithmicCorrelationBound
  change
    ((N - r - 1 : Nat) : Real) * (4 * t * r / A ^ 3) / (2 * Real.pi) + 2 |> fun q =>
      q * (2 * Real.pi / Real.sqrt (t * r / (8 * A ^ 3)) +
        2 * (Real.sqrt (t * r / (8 * A ^ 3)) /
          (t * r / (8 * A ^ 3)) + 1)) <= _
  have h32 : 4 * t * (r : Real) / A ^ 3 = 32 * x := by
    dsimp only [x]
    field_simp [hA.ne']
    ring
  rw [show t * (r : Real) / (8 * A ^ 3) = x by rfl, h32]
  exact hraw.trans hproduct

/-- Uniform correlation majorant on shifts below `H`. -/
noncomputable def simpleLogarithmicCorrelationBound
    (t A : Real) (N H : Nat) : Real :=
  let q := t / (8 * A ^ 3)
  100 * ((N : Real) * Real.sqrt (q * H) + 1 / Real.sqrt q)

theorem logarithmicCorrelationBound_le_uniform
    (t A : Real) (N H r : Nat) (ht : 0 < t) (hA : 0 < A)
    (hr : 0 < r) (hrH : r <= H)
    (hsmall : t * H / (8 * A ^ 3) <= 1) :
    logarithmicCorrelationBound t A N r <=
      simpleLogarithmicCorrelationBound t A N H := by
  let q : Real := t / (8 * A ^ 3)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hqr : t * (r : Real) / (8 * A ^ 3) = q * r := by
    dsimp only [q]
    ring
  have hqH : t * (H : Real) / (8 * A ^ 3) = q * H := by
    dsimp only [q]
    ring
  have hqrSmall : t * (r : Real) / (8 * A ^ 3) <= 1 := by
    calc
      t * (r : Real) / (8 * A ^ 3) <= t * (H : Real) / (8 * A ^ 3) := by gcongr
      _ <= 1 := hsmall
  have hbase := logarithmicCorrelationBound_le_simple t A N r ht hA hr hqrSmall
  have hrHReal : (r : Real) <= H := by exact_mod_cast hrH
  have honeR : (1 : Real) <= r := by exact_mod_cast hr
  have hsqrtHigh : Real.sqrt (q * r) <= Real.sqrt (q * H) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hrHReal hq.le
  have hsqrtLow : Real.sqrt q <= Real.sqrt (q * r) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hinv : 1 / Real.sqrt (q * r) <= 1 / Real.sqrt q :=
    one_div_le_one_div_of_le (Real.sqrt_pos.2 hq) hsqrtLow
  unfold simpleLogarithmicCorrelationBound
  dsimp only
  rw [hqr] at hbase
  exact hbase.trans (by gcongr)

/-- A-after-B estimate with a genuine uniform, rather than summed,
correlation majorant. -/
theorem logarithmic_weyl_AB_process_simple
    (t A : Real) (N H : Nat) (ht : 0 < t) (hA : 0 < A)
    (hH : H <= N) (hNA : (N : Real) <= A)
    (hsmall : t * H / (8 * A ^ 3) <= 1) :
    (H : Real) ^ 2 *
        ‖∑ n ∈ Finset.Ico (0 : Int) N, integerLogarithmicTerm t A n‖ ^ 2 <=
      ((N + H : Nat) : Real) *
        ((H : Real) * N + (H : Real) ^ 2 *
          simpleLogarithmicCorrelationBound t A N H) := by
  apply interval_weyl_differencing_complex
    (integerLogarithmicTerm t A) N H (simpleLogarithmicCorrelationBound t A N H)
  · intro n _hn
    simp
  · unfold simpleLogarithmicCorrelationBound
    positivity
  · intro h hh k hk hne
    have hbase := padded_logarithmic_correlation_norm_le
      t A N H h k ht hA hH hNA (Finset.mem_range.mp hh)
        (Finset.mem_range.mp hk) hne
    have hdistPos : 0 < shiftDistance h k := by
      unfold shiftDistance
      omega
    have hdistHigh : shiftDistance h k <= H := by
      unfold shiftDistance
      by_cases hle : h <= k
      · rw [Nat.sub_eq_zero_of_le hle, zero_add]
        exact (Nat.sub_le k h).trans (Nat.le_of_lt (Finset.mem_range.mp hk))
      · have kle : k <= h := Nat.le_of_not_ge hle
        rw [Nat.sub_eq_zero_of_le kle, add_zero]
        exact (Nat.sub_le h k).trans (Nat.le_of_lt (Finset.mem_range.mp hh))
    exact hbase.trans (logarithmicCorrelationBound_le_uniform
      t A N H (shiftDistance h k) ht hA hdistPos hdistHigh hsmall)

theorem simpleLogarithmicCorrelationBound_le_four_hundred
    (Y : Real) (A H : Nat) (hY : 1 <= Y) (hA : 0 < A)
    (hHY : (H : Real) * Y <= A) (hAY : (A : Real) ^ 2 <= Y ^ 3) :
    simpleLogarithmicCorrelationBound (Y ^ 3) A A H <= 400 * Y := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hAreal : 0 < (A : Real) := Nat.cast_pos.mpr hA
  let q : Real := Y ^ 3 / (8 * (A : Real) ^ 3)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hA_le_Y_sq : (A : Real) <= Y ^ 2 := by
    have hY3_le_Y4 : Y ^ 3 <= Y ^ 4 := by
      have := mul_le_mul_of_nonneg_left hY (pow_nonneg hYpos.le 3)
      nlinarith
    nlinarith [sq_nonneg ((A : Real) - Y ^ 2)]
  have hqH_le : q * H <= (Y / (A : Real)) ^ 2 := by
    dsimp only [q]
    rw [show Y ^ 3 / (8 * (A : Real) ^ 3) * (H : Real) =
      (Y ^ 3 * H) / (8 * (A : Real) ^ 3) by ring]
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : 0 < 8 * (A : Real) ^ 3)
      (by positivity : 0 < (A : Real) ^ 2)]
    calc
      Y ^ 3 * (H : Real) * (A : Real) ^ 2 =
          ((H : Real) * Y) * (Y ^ 2 * (A : Real) ^ 2) := by ring
      _ <= (A : Real) * (Y ^ 2 * (A : Real) ^ 2) :=
        mul_le_mul_of_nonneg_right hHY (mul_nonneg (pow_nonneg hYpos.le 2)
          (pow_nonneg hAreal.le 2))
      _ <= 8 * (A : Real) * (Y ^ 2 * (A : Real) ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith
        · positivity
      _ = Y ^ 2 * (8 * (A : Real) ^ 3) := by ring
  have hsqrtHigh : Real.sqrt (q * H) <= Y / (A : Real) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hqH_le⟩
  have hfirst : (A : Real) * Real.sqrt (q * H) <= Y := by
    calc
      (A : Real) * Real.sqrt (q * H) <= (A : Real) * (Y / (A : Real)) :=
        mul_le_mul_of_nonneg_left hsqrtHigh hAreal.le
      _ = Y := by field_simp
  have hA3_le_Y5 : (A : Real) ^ 3 <= Y ^ 5 := by
    calc
      (A : Real) ^ 3 = (A : Real) ^ 2 * A := by ring
      _ <= Y ^ 3 * Y ^ 2 := mul_le_mul hAY hA_le_Y_sq
        (Nat.cast_nonneg A) (pow_nonneg hYpos.le 3)
      _ = Y ^ 5 := by ring
  have hsquareLow : (1 / (3 * Y)) ^ 2 <= q := by
    dsimp only [q]
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : 0 < (3 * Y) ^ 2)
      (by positivity : 0 < 8 * (A : Real) ^ 3)]
    nlinarith [hA3_le_Y5, pow_nonneg hYpos.le 5]
  have hsqrtLow : 1 / (3 * Y) <= Real.sqrt q :=
    Real.le_sqrt_of_sq_le hsquareLow
  have hsecond : 1 / Real.sqrt q <= 3 * Y := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hq)]
    have hmul := mul_le_mul_of_nonneg_left hsqrtLow (by positivity : 0 <= 3 * Y)
    field_simp [hYpos.ne'] at hmul
    nlinarith
  unfold simpleLogarithmicCorrelationBound
  dsimp only
  change 100 * ((A : Real) * Real.sqrt (q * H) + 1 / Real.sqrt q) <= 400 * Y
  nlinarith

/-- Slack-bearing form of the uniform logarithmic correlation estimate.
The factor `X` records the precise amount by which the physical block may
cross the ideal Weyl boundary `A ^ 2 ≤ Y ^ 3`. -/
theorem simpleLogarithmicCorrelationBound_le_four_hundred_mul
    (Y X : Real) (A H : Nat) (hY : 1 ≤ Y) (hX : 1 ≤ X) (hA : 0 < A)
    (hHY : (H : Real) * Y ≤ A)
    (hAY : (A : Real) ^ 2 ≤ X * Y ^ 3) :
    simpleLogarithmicCorrelationBound (Y ^ 3) A A H ≤ 400 * X * Y := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hAreal : 0 < (A : Real) := Nat.cast_pos.mpr hA
  let q : Real := Y ^ 3 / (8 * (A : Real) ^ 3)
  have hq : 0 < q := by dsimp only [q]; positivity
  have hqH_le : q * H ≤ (Y / (A : Real)) ^ 2 := by
    dsimp only [q]
    rw [show Y ^ 3 / (8 * (A : Real) ^ 3) * (H : Real) =
      (Y ^ 3 * H) / (8 * (A : Real) ^ 3) by ring]
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : 0 < 8 * (A : Real) ^ 3)
      (by positivity : 0 < (A : Real) ^ 2)]
    calc
      Y ^ 3 * (H : Real) * (A : Real) ^ 2 =
          ((H : Real) * Y) * (Y ^ 2 * (A : Real) ^ 2) := by ring
      _ ≤ (A : Real) * (Y ^ 2 * (A : Real) ^ 2) :=
        mul_le_mul_of_nonneg_right hHY (mul_nonneg (pow_nonneg hYpos.le 2)
          (pow_nonneg hAreal.le 2))
      _ ≤ 8 * (A : Real) * (Y ^ 2 * (A : Real) ^ 2) := by
        apply mul_le_mul_of_nonneg_right
        · nlinarith
        · positivity
      _ = Y ^ 2 * (8 * (A : Real) ^ 3) := by ring
  have hsqrtHigh : Real.sqrt (q * H) ≤ Y / (A : Real) := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, hqH_le⟩
  have hfirst : (A : Real) * Real.sqrt (q * H) ≤ Y := by
    calc
      (A : Real) * Real.sqrt (q * H) ≤ (A : Real) * (Y / (A : Real)) :=
        mul_le_mul_of_nonneg_left hsqrtHigh hAreal.le
      _ = Y := by field_simp
  have hY3_le_Y4 : Y ^ 3 ≤ Y ^ 4 := by
    have := mul_le_mul_of_nonneg_left hY (pow_nonneg hYpos.le 3)
    nlinarith
  have hX_le_X2 : X ≤ X ^ 2 := by nlinarith
  have hA_le_XY2 : (A : Real) ≤ X * Y ^ 2 := by
    have hsquares : (A : Real) ^ 2 ≤ (X * Y ^ 2) ^ 2 := by
      calc
        (A : Real) ^ 2 ≤ X * Y ^ 3 := hAY
        _ ≤ X * Y ^ 4 := mul_le_mul_of_nonneg_left hY3_le_Y4 hXpos.le
        _ ≤ X ^ 2 * Y ^ 4 := mul_le_mul_of_nonneg_right hX_le_X2
          (pow_nonneg hYpos.le 4)
        _ = (X * Y ^ 2) ^ 2 := by ring
    nlinarith [sq_nonneg ((A : Real) - X * Y ^ 2)]
  have hA3_le : (A : Real) ^ 3 ≤ X ^ 2 * Y ^ 5 := by
    calc
      (A : Real) ^ 3 = (A : Real) ^ 2 * A := by ring
      _ ≤ (X * Y ^ 3) * (X * Y ^ 2) :=
        mul_le_mul hAY hA_le_XY2 hAreal.le (mul_nonneg hXpos.le (pow_nonneg hYpos.le 3))
      _ = X ^ 2 * Y ^ 5 := by ring
  have hsquareLow : (1 / (3 * X * Y)) ^ 2 ≤ q := by
    dsimp only [q]
    rw [div_pow]
    rw [div_le_div_iff₀ (by positivity : 0 < (3 * X * Y) ^ 2)
      (by positivity : 0 < 8 * (A : Real) ^ 3)]
    nlinarith [hA3_le, mul_nonneg (pow_nonneg hXpos.le 2) (pow_nonneg hYpos.le 5)]
  have hsqrtLow : 1 / (3 * X * Y) ≤ Real.sqrt q :=
    Real.le_sqrt_of_sq_le hsquareLow
  have hsecond : 1 / Real.sqrt q ≤ 3 * X * Y := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hq)]
    have hmul := mul_le_mul_of_nonneg_left hsqrtLow
      (by positivity : 0 ≤ 3 * X * Y)
    field_simp [hXpos.ne', hYpos.ne'] at hmul
    nlinarith
  unfold simpleLogarithmicCorrelationBound
  dsimp only
  change 100 * ((A : Real) * Real.sqrt (q * H) + 1 / Real.sqrt q) ≤
    400 * X * Y
  nlinarith [mul_pos hXpos hYpos]

/-- The classical `(1/6, 2/3)` Weyl estimate, written with `t = Y^3`.
The hypotheses describe the medium dyadic range `Y <= A <= Y^(3/2)`
and any integer shift length within a factor two of `A / Y`. -/
theorem logarithmic_weyl_exponent_pair_with_shift
    (Y : Real) (A H : Nat) (hY : 1 <= Y) (hA : 0 < A) (hH : 0 < H)
    (hYA : Y <= A) (hAY : (A : Real) ^ 2 <= Y ^ 3)
    (hHY : (H : Real) * Y <= A) (hAH : (A : Real) <= 2 * H * Y) :
    ‖logarithmicSum (Y ^ 3) A (A + A)‖ <=
      30 * Real.sqrt ((A : Real) * Y) := by
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hAreal : 0 < (A : Real) := Nat.cast_pos.mpr hA
  have hHreal : 0 < (H : Real) := Nat.cast_pos.mpr hH
  have hHleReal : (H : Real) <= A := by
    calc
      (H : Real) = (H : Real) * 1 := by ring
      _ <= (H : Real) * Y :=
        mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg H)
      _ <= A := hHY
  have hHle : H <= A := by exact_mod_cast hHleReal
  have hsmall : Y ^ 3 * (H : Real) / (8 * (A : Real) ^ 3) <= 1 := by
    rw [div_le_one (by positivity : 0 < 8 * (A : Real) ^ 3)]
    calc
      Y ^ 3 * (H : Real) = ((H : Real) * Y) * Y ^ 2 := by ring
      _ <= (A : Real) * Y ^ 2 :=
        mul_le_mul_of_nonneg_right hHY (pow_nonneg hYpos.le 2)
      _ <= (A : Real) * (A : Real) ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith
        · exact hAreal.le
      _ <= 8 * (A : Real) ^ 3 := by nlinarith [pow_pos hAreal 3]
  have hab := logarithmic_weyl_AB_process_simple
    (Y ^ 3) A A H (pow_pos hYpos 3) hAreal hHle (by rfl) hsmall
  rw [integerLogarithmicSum_eq] at hab
  have hc := simpleLogarithmicCorrelationBound_le_four_hundred Y A H hY hA hHY hAY
  have hab' :
      (H : Real) ^ 2 * ‖logarithmicSum (Y ^ 3) A (A + A)‖ ^ 2 <=
        (((A + H : Nat) : Real) *
          ((H : Real) * A + (H : Real) ^ 2 * (400 * Y))) := by
    exact hab.trans (by gcongr)
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at hab'
  have houter : (A : Real) + H <= 2 * A := by nlinarith
  have hinner : (H : Real) * A + (H : Real) ^ 2 * (400 * Y) <=
      402 * (H : Real) ^ 2 * Y := by
    have hHA : (H : Real) * A <= 2 * (H : Real) ^ 2 * Y := by
      have := mul_le_mul_of_nonneg_left hAH (Nat.cast_nonneg H)
      nlinarith
    nlinarith [mul_nonneg (sq_nonneg (H : Real)) hYpos.le]
  have hrightNonneg : 0 <=
      (H : Real) * A + (H : Real) ^ 2 * (400 * Y) := by positivity
  have hbound :
      (((A : Real) + H) *
          ((H : Real) * A + (H : Real) ^ 2 * (400 * Y))) <=
        900 * (H : Real) ^ 2 * A * Y := by
    calc
      ((A : Real) + H) *
          ((H : Real) * A + (H : Real) ^ 2 * (400 * Y)) <=
          (2 * A) * ((H : Real) * A + (H : Real) ^ 2 * (400 * Y)) :=
        mul_le_mul_of_nonneg_right houter hrightNonneg
      _ <= (2 * A) * (402 * (H : Real) ^ 2 * Y) :=
        mul_le_mul_of_nonneg_left hinner (by positivity)
      _ <= 900 * (H : Real) ^ 2 * A * Y := by
        have hnonneg := mul_nonneg (mul_nonneg (sq_nonneg (H : Real)) hAreal.le) hYpos.le
        nlinarith
  have hsq : ‖logarithmicSum (Y ^ 3) A (A + A)‖ ^ 2 <=
      900 * (A : Real) * Y := by
    have := hab'.trans hbound
    nlinarith [sq_pos_of_pos hHreal]
  have hsqrtSq : Real.sqrt ((A : Real) * Y) ^ 2 = (A : Real) * Y :=
    Real.sq_sqrt (mul_nonneg hAreal.le hYpos.le)
  have hsqrtNonneg : 0 <= Real.sqrt ((A : Real) * Y) := Real.sqrt_nonneg _
  nlinarith [norm_nonneg (logarithmicSum (Y ^ 3) A (A + A))]

/-- Integer shift realizing the classical choice `A / Y` when `t = Y^3`. -/
noncomputable def classicalWeylShiftLength (Y : Real) (A : Nat) : Nat :=
  Nat.floor ((A : Real) / Y)

theorem classicalWeylShiftLength_spec
    (Y : Real) (A : Nat) (hY : 1 <= Y) (hA : 0 < A) (hYA : Y <= A) :
    let H := classicalWeylShiftLength Y A
    0 < H ∧ H <= A ∧ (H : Real) * Y <= A ∧ (A : Real) <= 2 * H * Y := by
  dsimp only [classicalWeylShiftLength]
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hxOne : (1 : Real) <= (A : Real) / Y := by
    rw [le_div_iff₀ hYpos]
    simpa only [one_mul] using hYA
  have hpos : 0 < Nat.floor ((A : Real) / Y) := Nat.floor_pos.mpr hxOne
  have hfloor : ((Nat.floor ((A : Real) / Y) : Nat) : Real) <= (A : Real) / Y :=
    Nat.floor_le (by positivity)
  have hHY : ((Nat.floor ((A : Real) / Y) : Nat) : Real) * Y <= A := by
    calc
      ((Nat.floor ((A : Real) / Y) : Nat) : Real) * Y <= ((A : Real) / Y) * Y :=
        mul_le_mul_of_nonneg_right hfloor hYpos.le
      _ = A := by field_simp
  have hHle : Nat.floor ((A : Real) / Y) <= A := by
    have hcast : ((Nat.floor ((A : Real) / Y) : Nat) : Real) <= A := by
      calc
        ((Nat.floor ((A : Real) / Y) : Nat) : Real) <=
            ((Nat.floor ((A : Real) / Y) : Nat) : Real) * Y := by
          calc
            ((Nat.floor ((A : Real) / Y) : Nat) : Real) =
                ((Nat.floor ((A : Real) / Y) : Nat) : Real) * 1 := by ring
            _ <= _ := mul_le_mul_of_nonneg_left hY (Nat.cast_nonneg _)
        _ <= A := hHY
    exact_mod_cast hcast
  have hxLt : (A : Real) / Y <
      ((Nat.floor ((A : Real) / Y) + 1 : Nat) : Real) :=
    by simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one ((A : Real) / Y))
  have hfloorOne : (1 : Real) <= ((Nat.floor ((A : Real) / Y) : Nat) : Real) := by
    exact_mod_cast hpos
  have hxTwo : (A : Real) / Y <=
      2 * ((Nat.floor ((A : Real) / Y) : Nat) : Real) := by
    push_cast at hxLt
    linarith
  have hAH : (A : Real) <=
      2 * ((Nat.floor ((A : Real) / Y) : Nat) : Real) * Y := by
    rw [← div_le_iff₀ hYpos]
    exact hxTwo
  exact ⟨hpos, hHle, hHY, hAH⟩

/-- Assumption-free shift selection for the classical `(1/6, 2/3)`
logarithmic Weyl estimate. -/
theorem logarithmic_weyl_exponent_pair
    (Y : Real) (A : Nat) (hY : 1 <= Y) (hA : 0 < A)
    (hYA : Y <= A) (hAY : (A : Real) ^ 2 <= Y ^ 3) :
    ‖logarithmicSum (Y ^ 3) A (A + A)‖ <=
      30 * Real.sqrt ((A : Real) * Y) := by
  obtain ⟨hH, _hHle, hHY, hAH⟩ := classicalWeylShiftLength_spec Y A hY hA hYA
  exact logarithmic_weyl_exponent_pair_with_shift
    Y A (classicalWeylShiftLength Y A) hY hA hH hYA hAY hHY hAH

/-- Uniform prefix form of the `(1/6, 2/3)` bound, needed for Abel
summation of the critical-line weight. -/
theorem logarithmic_weyl_exponent_pair_prefix
    (Y : Real) (A N : Nat) (hY : 1 <= Y) (hA : 0 < A)
    (hYA : Y <= A) (hAY : (A : Real) ^ 2 <= Y ^ 3) (hNA : N <= A) :
    ‖logarithmicSum (Y ^ 3) A (A + N)‖ <=
      30 * Real.sqrt ((A : Real) * Y) := by
  obtain ⟨hH, hHle, hHY, hAH⟩ := classicalWeylShiftLength_spec Y A hY hA hYA
  let H := classicalWeylShiftLength Y A
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hAreal : 0 < (A : Real) := Nat.cast_pos.mpr hA
  have hHreal : 0 < (H : Real) := Nat.cast_pos.mpr hH
  have hNreal : (N : Real) <= A := by exact_mod_cast hNA
  have hsqrtSq : Real.sqrt ((A : Real) * Y) ^ 2 = (A : Real) * Y :=
    Real.sq_sqrt (mul_nonneg hAreal.le hYpos.le)
  have hsqrtNonneg : 0 <= Real.sqrt ((A : Real) * Y) := Real.sqrt_nonneg _
  by_cases hHN : H <= N
  · have hsmall : Y ^ 3 * (H : Real) / (8 * (A : Real) ^ 3) <= 1 := by
      rw [div_le_one (by positivity : 0 < 8 * (A : Real) ^ 3)]
      calc
        Y ^ 3 * (H : Real) = ((H : Real) * Y) * Y ^ 2 := by ring
        _ <= (A : Real) * Y ^ 2 :=
          mul_le_mul_of_nonneg_right hHY (pow_nonneg hYpos.le 2)
        _ <= (A : Real) * (A : Real) ^ 2 := by
          apply mul_le_mul_of_nonneg_left
          · nlinarith
          · exact hAreal.le
        _ <= 8 * (A : Real) ^ 3 := by nlinarith [pow_pos hAreal 3]
    have hab := logarithmic_weyl_AB_process_simple
      (Y ^ 3) A N H (pow_pos hYpos 3) hAreal hHN hNreal hsmall
    rw [integerLogarithmicSum_eq] at hab
    have hcA := simpleLogarithmicCorrelationBound_le_four_hundred
      Y A H hY hA hHY hAY
    have hcN : simpleLogarithmicCorrelationBound (Y ^ 3) A N H <= 400 * Y := by
      exact (show simpleLogarithmicCorrelationBound (Y ^ 3) A N H <=
          simpleLogarithmicCorrelationBound (Y ^ 3) A A H by
        unfold simpleLogarithmicCorrelationBound
        dsimp only
        apply mul_le_mul_of_nonneg_left
        · let s := Real.sqrt (Y ^ 3 / (8 * (A : Real) ^ 3) * (H : Real))
          have hm : (N : Real) * s <= (A : Real) * s :=
            mul_le_mul_of_nonneg_right hNreal (Real.sqrt_nonneg _)
          dsimp only [s] at hm
          linarith
        · norm_num).trans hcA
    have hab' :
        (H : Real) ^ 2 * ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 <=
          (((N + H : Nat) : Real) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * Y))) := by
      exact hab.trans (by gcongr)
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at hab'
    have houter : (N : Real) + H <= 2 * A := by
      have hHcast : (H : Real) <= A := by exact_mod_cast hHle
      nlinarith
    have hinner : (H : Real) * N + (H : Real) ^ 2 * (400 * Y) <=
        402 * (H : Real) ^ 2 * Y := by
      have hHA : (H : Real) * N <= 2 * (H : Real) ^ 2 * Y := by
        have hNAH := hNreal.trans hAH
        have := mul_le_mul_of_nonneg_left hNAH (Nat.cast_nonneg H)
        nlinarith
      nlinarith [mul_nonneg (sq_nonneg (H : Real)) hYpos.le]
    have hrightNonneg : 0 <=
        (H : Real) * N + (H : Real) ^ 2 * (400 * Y) := by positivity
    have hbound :
        (((N : Real) + H) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * Y))) <=
          900 * (H : Real) ^ 2 * A * Y := by
      calc
        ((N : Real) + H) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * Y)) <=
            (2 * A) * ((H : Real) * N + (H : Real) ^ 2 * (400 * Y)) :=
          mul_le_mul_of_nonneg_right houter hrightNonneg
        _ <= (2 * A) * (402 * (H : Real) ^ 2 * Y) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
        _ <= 900 * (H : Real) ^ 2 * A * Y := by
          have hnonneg := mul_nonneg (mul_nonneg (sq_nonneg (H : Real)) hAreal.le) hYpos.le
          nlinarith
    have hsq : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 <=
        900 * (A : Real) * Y := by
      have := hab'.trans hbound
      nlinarith [sq_pos_of_pos hHreal]
    nlinarith [norm_nonneg (logarithmicSum (Y ^ 3) A (A + N))]
  · have hNH : N < H := Nat.lt_of_not_ge hHN
    have htrivial := norm_logarithmicSum_le_length (Y ^ 3) A (A + N)
    have hlength : (A + N - A : Nat) = N := by omega
    rw [hlength] at htrivial
    have hHYsq : ((H : Real) * Y) ^ 2 <= (A : Real) ^ 2 := by
      nlinarith [sq_nonneg ((A : Real) - (H : Real) * Y)]
    have hHsqY : (H : Real) ^ 2 <= Y := by
      have hmul : Y ^ 2 * (H : Real) ^ 2 <= Y ^ 2 * Y := by
        calc
          Y ^ 2 * (H : Real) ^ 2 = ((H : Real) * Y) ^ 2 := by ring
          _ <= (A : Real) ^ 2 := hHYsq
          _ <= Y ^ 3 := hAY
          _ = Y ^ 2 * Y := by ring
      by_contra hnot
      have hlt : Y < (H : Real) ^ 2 := lt_of_not_ge hnot
      have hcontra := mul_lt_mul_of_pos_left hlt (sq_pos_of_pos hYpos)
      exact (not_lt_of_ge hmul) hcontra
    have hHsqAY : (H : Real) ^ 2 <= (A : Real) * Y := by
      calc
        (H : Real) ^ 2 <= Y := hHsqY
        _ <= (A : Real) * Y := by
          have hAone : (1 : Real) <= A := by exact_mod_cast hA
          nlinarith
    have hNlt : (N : Real) < H := by exact_mod_cast hNH
    have hnorm : ‖logarithmicSum (Y ^ 3) A (A + N)‖ <= H := htrivial.trans hNlt.le
    have hnormSq : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 <= (A : Real) * Y := by
      nlinarith [norm_nonneg (logarithmicSum (Y ^ 3) A (A + N))]
    nlinarith [norm_nonneg (logarithmicSum (Y ^ 3) A (A + N))]

/-- Uniform prefix Weyl estimate with an explicit multiplicative boundary
slack.  This is the source-faithful form needed after the floored reflected
cutoff, where the ideal relation `A ^ 2 ≤ Y ^ 3` is enlarged by a known
power of the ambient height. -/
theorem logarithmic_weyl_exponent_pair_prefix_with_slack
    (Y X : Real) (A N : Nat) (hY : 1 ≤ Y) (hX : 1 ≤ X) (hA : 0 < A)
    (hYA : Y ≤ A) (hAY : (A : Real) ^ 2 ≤ X * Y ^ 3) (hNA : N ≤ A) :
    ‖logarithmicSum (Y ^ 3) A (A + N)‖ ≤
      30 * Real.sqrt (X * (A : Real) * Y) := by
  obtain ⟨hH, hHle, hHY, hAH⟩ := classicalWeylShiftLength_spec Y A hY hA hYA
  let H := classicalWeylShiftLength Y A
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hAreal : 0 < (A : Real) := Nat.cast_pos.mpr hA
  have hHreal : 0 < (H : Real) := Nat.cast_pos.mpr hH
  have hNreal : (N : Real) ≤ A := by exact_mod_cast hNA
  have hsqrtSq : Real.sqrt (X * (A : Real) * Y) ^ 2 = X * (A : Real) * Y :=
    Real.sq_sqrt (by positivity)
  by_cases hHN : H ≤ N
  · have hsmall : Y ^ 3 * (H : Real) / (8 * (A : Real) ^ 3) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < 8 * (A : Real) ^ 3)]
      calc
        Y ^ 3 * (H : Real) = ((H : Real) * Y) * Y ^ 2 := by ring
        _ ≤ (A : Real) * Y ^ 2 :=
          mul_le_mul_of_nonneg_right hHY (pow_nonneg hYpos.le 2)
        _ ≤ (A : Real) * (A : Real) ^ 2 := by
          apply mul_le_mul_of_nonneg_left
          · nlinarith
          · exact hAreal.le
        _ ≤ 8 * (A : Real) ^ 3 := by nlinarith [pow_pos hAreal 3]
    have hab := logarithmic_weyl_AB_process_simple
      (Y ^ 3) A N H (pow_pos hYpos 3) hAreal hHN hNreal hsmall
    rw [integerLogarithmicSum_eq] at hab
    have hcA := simpleLogarithmicCorrelationBound_le_four_hundred_mul
      Y X A H hY hX hA hHY hAY
    have hcN : simpleLogarithmicCorrelationBound (Y ^ 3) A N H ≤
        400 * X * Y := by
      exact (show simpleLogarithmicCorrelationBound (Y ^ 3) A N H ≤
          simpleLogarithmicCorrelationBound (Y ^ 3) A A H by
        unfold simpleLogarithmicCorrelationBound
        dsimp only
        apply mul_le_mul_of_nonneg_left
        · let s := Real.sqrt (Y ^ 3 / (8 * (A : Real) ^ 3) * (H : Real))
          have hm : (N : Real) * s ≤ (A : Real) * s :=
            mul_le_mul_of_nonneg_right hNreal (Real.sqrt_nonneg _)
          dsimp only [s] at hm
          linarith
        · norm_num).trans hcA
    have hab' :
        (H : Real) ^ 2 * ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 ≤
          (((N + H : Nat) : Real) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * X * Y))) := by
      exact hab.trans (by gcongr)
    norm_num only [Nat.cast_add, Nat.cast_ofNat] at hab'
    have houter : (N : Real) + H ≤ 2 * A := by
      have hHcast : (H : Real) ≤ A := by exact_mod_cast hHle
      nlinarith
    have hinner : (H : Real) * N + (H : Real) ^ 2 * (400 * X * Y) ≤
        402 * X * (H : Real) ^ 2 * Y := by
      have hHA : (H : Real) * N ≤ 2 * (H : Real) ^ 2 * Y := by
        have hNAH := hNreal.trans hAH
        have := mul_le_mul_of_nonneg_left hNAH (Nat.cast_nonneg H)
        nlinarith
      have hFirst : 2 * (H : Real) ^ 2 * Y ≤
          2 * X * (H : Real) ^ 2 * Y := by
        have hNonneg : 0 ≤ 2 * (H : Real) ^ 2 * Y := by positivity
        nlinarith
      nlinarith [mul_nonneg (sq_nonneg (H : Real)) hYpos.le]
    have hrightNonneg : 0 ≤
        (H : Real) * N + (H : Real) ^ 2 * (400 * X * Y) := by positivity
    have hbound :
        (((N : Real) + H) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * X * Y))) ≤
          900 * (H : Real) ^ 2 * X * A * Y := by
      calc
        ((N : Real) + H) *
            ((H : Real) * N + (H : Real) ^ 2 * (400 * X * Y)) ≤
            (2 * A) * ((H : Real) * N +
              (H : Real) ^ 2 * (400 * X * Y)) :=
          mul_le_mul_of_nonneg_right houter hrightNonneg
        _ ≤ (2 * A) * (402 * X * (H : Real) ^ 2 * Y) :=
          mul_le_mul_of_nonneg_left hinner (by positivity)
        _ ≤ 900 * (H : Real) ^ 2 * X * A * Y := by
          have hnonneg := mul_nonneg
            (mul_nonneg (mul_nonneg (sq_nonneg (H : Real)) hXpos.le) hAreal.le)
            hYpos.le
          nlinarith
    have hsq : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 ≤
        900 * (X * (A : Real) * Y) := by
      have := hab'.trans hbound
      nlinarith [sq_pos_of_pos hHreal]
    nlinarith [norm_nonneg (logarithmicSum (Y ^ 3) A (A + N)),
      Real.sqrt_nonneg (X * (A : Real) * Y)]
  · have hNH : N < H := Nat.lt_of_not_ge hHN
    have htrivial := norm_logarithmicSum_le_length (Y ^ 3) A (A + N)
    have hlength : (A + N - A : Nat) = N := by omega
    rw [hlength] at htrivial
    have hHYsq : ((H : Real) * Y) ^ 2 ≤ (A : Real) ^ 2 := by
      nlinarith [sq_nonneg ((A : Real) - (H : Real) * Y)]
    have hHsqY : (H : Real) ^ 2 ≤ X * Y := by
      have hmul : Y ^ 2 * (H : Real) ^ 2 ≤ Y ^ 2 * (X * Y) := by
        calc
          Y ^ 2 * (H : Real) ^ 2 = ((H : Real) * Y) ^ 2 := by ring
          _ ≤ (A : Real) ^ 2 := hHYsq
          _ ≤ X * Y ^ 3 := hAY
          _ = Y ^ 2 * (X * Y) := by ring
      by_contra hnot
      have hlt : X * Y < (H : Real) ^ 2 := lt_of_not_ge hnot
      have hcontra := mul_lt_mul_of_pos_left hlt (sq_pos_of_pos hYpos)
      exact (not_lt_of_ge hmul) hcontra
    have hHsqXAY : (H : Real) ^ 2 ≤ X * (A : Real) * Y := by
      calc
        (H : Real) ^ 2 ≤ X * Y := hHsqY
        _ ≤ X * (A : Real) * Y := by
          have hAone : (1 : Real) ≤ A := by exact_mod_cast hA
          nlinarith [mul_pos hXpos hYpos]
    have hNlt : (N : Real) < H := by exact_mod_cast hNH
    have hnorm : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ≤ H :=
      htrivial.trans hNlt.le
    have hnormSq : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ^ 2 ≤
        X * (A : Real) * Y := by
      nlinarith [norm_nonneg (logarithmicSum (Y ^ 3) A (A + N))]
    have hsqrtBound : ‖logarithmicSum (Y ^ 3) A (A + N)‖ ≤
        Real.sqrt (X * (A : Real) * Y) := Real.le_sqrt_of_sq_le hnormSq
    calc
      ‖logarithmicSum (Y ^ 3) A (A + N)‖ ≤
          Real.sqrt (X * (A : Real) * Y) := hsqrtBound
      _ ≤ 30 * Real.sqrt (X * (A : Real) * Y) := by
        nlinarith [Real.sqrt_nonneg (X * (A : Real) * Y)]

end RiemannZeta.GuthMaynard
