module
public import GuthMaynard.VanDerCorput

@[expose] public section

open Complex Finset Set
open scoped BigOperators

namespace RiemannZeta.GuthMaynard

/-!
# Multi-period van der Corput second-derivative estimate

This module partitions a monotone sequence of phase increments into full
`2 * pi` periods.  Kusmin--Landau controls the interior of every period;
the lower second-difference bound counts the two short endpoint pieces.
-/

theorem discrete_growth_lower (theta : Nat -> Real) (lambda : Real)
    (i d N : Nat)
    (hstep : forall n, n < N -> lambda <= theta (n + 1) - theta n)
    (hid : i + d <= N) :
    (d : Real) * lambda <= theta (i + d) - theta i := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd : i + d <= N := by omega
      have hih := ih hd
      have hs := hstep (i + d) (by omega)
      rw [show i + (d + 1) = i + d + 1 by omega]
      push_cast
      linarith

theorem monotone_of_step (theta : Nat -> Real) (N : Nat)
    (hstep : forall n, n < N -> theta n <= theta (n + 1)) :
    forall i j, i <= j -> j <= N -> theta i <= theta j := by
  intro i j hij hj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  induction d with
  | zero => simp
  | succ d ih =>
      have hprev := ih (by omega) (by omega)
      exact hprev.trans (hstep (i + d) (by omega))

theorem filter_card_bound (theta : Nat -> Real) (N : Nat)
    (lambda a b : Real) (hlambda : 0 < lambda) (hab : a <= b)
    (hstep : forall n, n < N -> lambda <= theta (n + 1) - theta n) :
    (((Finset.range (N + 1)).filter fun n => a <= theta n ∧ theta n <= b).card : Real)
      <= (b - a) / lambda + 1 := by
  let s := (Finset.range (N + 1)).filter fun n => a <= theta n ∧ theta n <= b
  by_cases hs : s.Nonempty
  · let i := s.min' hs
    let j := s.max' hs
    have hi_mem : i ∈ s := s.min'_mem hs
    have hj_mem : j ∈ s := s.max'_mem hs
    have hi_data := Finset.mem_filter.mp hi_mem
    have hj_data := Finset.mem_filter.mp hj_mem
    have hij : i <= j := s.min'_le j hj_mem
    have hjN : j <= N := by
      have := Finset.mem_range.mp hj_data.1
      omega
    have hsub : s ⊆ Finset.Icc i j := by
      intro n hn
      exact Finset.mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
    have hcard : s.card <= (Finset.Icc i j).card := Finset.card_le_card hsub
    have hgap := discrete_growth_lower theta lambda i (j - i) N hstep (by omega)
    rw [Nat.card_Icc] at hcard
    have hcast : (s.card : Real) <= ((j + 1 - i : Nat) : Real) := by exact_mod_cast hcard
    have hji : i + (j - i) = j := by omega
    rw [hji] at hgap
    have hwidth : theta j - theta i <= b - a := by linarith [hi_data.2.1, hj_data.2.2]
    have hnat : ((j + 1 - i : Nat) : Real) = (j - i : Nat) + 1 := by
      norm_cast
      omega
    rw [hnat] at hcast
    calc
      (s.card : Real) <= (j - i : Nat) + 1 := hcast
      _ <= (b - a) / lambda + 1 := by
        rw [add_le_add_iff_right]
        rw [le_div_iff₀ hlambda]
        exact hgap.trans hwidth
  · change (s.card : Real) <= _
    rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hnonneg : 0 <= (b - a) / lambda :=
      div_nonneg (sub_nonneg.mpr hab) hlambda.le
    linarith

theorem sum_Icc_eq_shifted_range (z : Nat -> Complex) (i j : Nat) (hij : i <= j) :
    (∑ n ∈ Finset.Icc i j, z n) = ∑ d ∈ Finset.range (j - i + 1), z (i + d) := by
  symm
  apply Finset.sum_bij (fun d _hd => i + d)
  case hi =>
    intro d hd
    apply Finset.mem_Icc.mpr
    have hd' := Finset.mem_range.mp hd
    omega
  case i_inj =>
    intro d₁ _hd₁ d₂ _hd₂ heq
    omega
  case i_surj =>
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    refine ⟨n - i, ?_, by omega⟩
    exact Finset.mem_range.mpr (by omega)
  case h =>
    intro d _hd
    rfl

theorem kusminLandau_good_fiber (f : Nat -> Real) (N : Nat) (k : Int)
    (delta : Real) (hdelta : 0 < delta)
    (hmono : forall n, n < N ->
      f (n + 1) - f n <= f (n + 2) - f (n + 1)) :
    ‖∑ n ∈ (Finset.range (N + 1)).filter (fun n =>
        delta <= f (n + 1) - f n - (k : Real) * (2 * Real.pi) ∧
        f (n + 1) - f n - (k : Real) * (2 * Real.pi) <= 2 * Real.pi - delta),
      unitaryPhase (f n)‖ <= 2 * Real.pi / delta := by
  let s := (Finset.range (N + 1)).filter (fun n =>
    delta <= f (n + 1) - f n - (k : Real) * (2 * Real.pi) ∧
    f (n + 1) - f n - (k : Real) * (2 * Real.pi) <= 2 * Real.pi - delta)
  by_cases hs : s.Nonempty
  · let i := s.min' hs
    let j := s.max' hs
    have hi_mem : i ∈ s := s.min'_mem hs
    have hj_mem : j ∈ s := s.max'_mem hs
    have hij : i <= j := s.min'_le j hj_mem
    have hi_data := Finset.mem_filter.mp hi_mem
    have hj_data := Finset.mem_filter.mp hj_mem
    have hjN : j <= N := by
      have := Finset.mem_range.mp hj_data.1
      omega
    have hs_eq : s = Finset.Icc i j := by
      ext n
      constructor
      · intro hn
        exact Finset.mem_Icc.mpr ⟨s.min'_le n hn, s.le_max' n hn⟩
      · intro hn
        have hn' := Finset.mem_Icc.mp hn
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_range.mpr (by omega)
        · have hleft := monotone_of_step
              (fun m => f (m + 1) - f m) N hmono i n hn'.1 (by omega)
          have hright := monotone_of_step
              (fun m => f (m + 1) - f m) N hmono n j hn'.2 hjN
          constructor <;> linarith [hi_data.2.1, hj_data.2.2]
    change ‖∑ n ∈ s, unitaryPhase (f n)‖ <= _
    rw [hs_eq, sum_Icc_eq_shifted_range _ i j hij]
    apply kusminLandau_interval f i (j - i) k delta hdelta
    · intro d hd
      have hd_mem : i + d ∈ s := by
        rw [hs_eq]
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      exact (Finset.mem_filter.mp hd_mem).2.1
    · intro d hd
      have hd_mem : i + d ∈ s := by
        rw [hs_eq]
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      exact (Finset.mem_filter.mp hd_mem).2.2
    · intro d hd
      exact hmono (i + d) (by omega)
  · change ‖∑ n ∈ s, unitaryPhase (f n)‖ <= _
    rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp only [Finset.sum_empty, norm_zero]
    positivity

/-- The `periodIndex` definition used by the source-facing construction in `SecondDerivative`. -/
noncomputable def periodIndex (theta : Real) : Int :=
  Int.floor (theta / (2 * Real.pi))

theorem periodIndex_bounds (theta : Real) :
    (periodIndex theta : Real) * (2 * Real.pi) <= theta ∧
      theta < ((periodIndex theta : Real) + 1) * (2 * Real.pi) := by
  have hp : 0 < 2 * Real.pi := by positivity
  constructor
  · rw [periodIndex]
    have h := Int.floor_le (theta / (2 * Real.pi))
    exact (le_div_iff₀ hp).mp (by simpa [mul_comm] using h)
  · rw [periodIndex]
    have h := Int.lt_floor_add_one (theta / (2 * Real.pi))
    exact (div_lt_iff₀ hp).mp h

theorem periodIndex_mono {x y : Real} (hxy : x <= y) :
    periodIndex x <= periodIndex y := by
  apply Int.floor_mono
  exact div_le_div_of_nonneg_right hxy (by positivity)

theorem period_count_bound {x y : Real} (hxy : x <= y) :
    (((Finset.Icc (periodIndex x) (periodIndex y)).card : Nat) : Real)
      <= (y - x) / (2 * Real.pi) + 2 := by
  let i := periodIndex x
  let j := periodIndex y
  have hij : i <= j := periodIndex_mono hxy
  have hcardInt : ((Finset.Icc i j).card : Int) = j + 1 - i :=
    Int.card_Icc_of_le i j (by omega)
  have hcardReal : (((Finset.Icc i j).card : Nat) : Real) = (j : Real) + 1 - (i : Real) := by
    exact_mod_cast hcardInt
  have hifloor : (i : Real) <= x / (2 * Real.pi) := by
    exact Int.floor_le _
  have hilower : x / (2 * Real.pi) < (i : Real) + 1 := by
    exact Int.lt_floor_add_one _
  have hjfloor : (j : Real) <= y / (2 * Real.pi) := by
    exact Int.floor_le _
  rw [show Finset.Icc (periodIndex x) (periodIndex y) = Finset.Icc i j by rfl,
    hcardReal]
  have hp : 0 < 2 * Real.pi := by positivity
  have hdiv : y / (2 * Real.pi) - x / (2 * Real.pi) =
      (y - x) / (2 * Real.pi) := by ring
  rw [← hdiv]
  linarith

theorem discrete_growth_upper (theta : Nat -> Real) (Lambda : Real)
    (i d N : Nat)
    (hstep : forall n, n < N -> theta (n + 1) - theta n <= Lambda)
    (hid : i + d <= N) :
    theta (i + d) - theta i <= (d : Real) * Lambda := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hd : i + d <= N := by omega
      have hih := ih hd
      have hs := hstep (i + d) (by omega)
      rw [show i + (d + 1) = i + d + 1 by omega]
      push_cast
      linarith

theorem norm_phase_sum_finset_le_card (s : Finset Nat) (f : Nat -> Real) :
    ‖∑ n ∈ s, unitaryPhase (f n)‖ <= (s.card : Real) := by
  calc
    ‖∑ n ∈ s, unitaryPhase (f n)‖ <= ∑ n ∈ s, ‖unitaryPhase (f n)‖ :=
      norm_sum_le _ _
    _ = (s.card : Real) := by simp

theorem vanDerCorput_second_derivative
    (f : Nat -> Real) (N : Nat) (lambda Lambda delta : Real)
    (hlambda : 0 < lambda) (hdelta : 0 < delta)
    (hlower : forall n, n < N ->
      lambda <= (f (n + 2) - f (n + 1)) - (f (n + 1) - f n))
    (hupper : forall n, n < N ->
      (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) <= Lambda) :
    ‖∑ n ∈ Finset.range (N + 1), unitaryPhase (f n)‖ <=
      ((N : Real) * Lambda / (2 * Real.pi) + 2) *
        (2 * Real.pi / delta + 2 * (delta / lambda + 1)) := by
  let theta : Nat -> Real := fun n => f (n + 1) - f n
  let idx : Nat -> Int := fun n => periodIndex (theta n)
  let K := Finset.Icc (idx 0) (idx N)
  let base := Finset.range (N + 1)
  let good : Int -> Nat -> Prop := fun k n =>
    delta <= theta n - (k : Real) * (2 * Real.pi) ∧
      theta n - (k : Real) * (2 * Real.pi) <= 2 * Real.pi - delta
  let fiber : Int -> Finset Nat := fun k => base.filter (fun n => idx n = k)
  have hmono : forall i j, i <= j -> j <= N -> theta i <= theta j := by
    exact monotone_of_step theta N
      (fun n hn => by dsimp only [theta]; linarith [hlower n hn])
  have hidx_mem : forall n, n ∈ base -> idx n ∈ K := by
    intro n hn
    have hnN : n <= N := by
      have := Finset.mem_range.mp hn
      omega
    apply Finset.mem_Icc.mpr
    exact ⟨periodIndex_mono (hmono 0 n (by omega) hnN),
      periodIndex_mono (hmono n N hnN le_rfl)⟩
  have hpartition :
      (∑ k ∈ K, ∑ n ∈ fiber k, unitaryPhase (f n)) =
        ∑ n ∈ base, unitaryPhase (f n) := by
    simp only [fiber, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    have hmem := hidx_mem n hn
    calc
      ∑ k ∈ K, (if idx n = k then unitaryPhase (f n) else 0) =
          ∑ k ∈ K, (if k = idx n then unitaryPhase (f n) else 0) := by
            apply Finset.sum_congr rfl
            intro k _hk
            by_cases h : k = idx n
            · simp [h]
            · have h' : ¬ idx n = k := fun he => h he.symm
              simp [h, h']
      _ = unitaryPhase (f n) := by simp [hmem]
  have hgood_subset (k : Int) : base.filter (good k) ⊆ fiber k := by
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨hnData.1, ?_⟩
    have hlow : (k : Real) <= theta n / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
      linarith [hnData.2.1]
    have hhigh : theta n / (2 * Real.pi) < (k : Real) + 1 := by
      rw [div_lt_iff₀ (by positivity : 0 < 2 * Real.pi)]
      linarith [hnData.2.2, hdelta]
    dsimp only [idx, periodIndex]
    exact Int.floor_eq_iff.mpr ⟨hlow, hhigh⟩
  have hfiber (k : Int) (hk : k ∈ K) :
      ‖∑ n ∈ fiber k, unitaryPhase (f n)‖ <=
        2 * Real.pi / delta + 2 * (delta / lambda + 1) := by
    let bad := (fiber k).filter (fun n => ¬ good k n)
    let low := base.filter (fun n =>
      (k : Real) * (2 * Real.pi) <= theta n ∧
        theta n <= (k : Real) * (2 * Real.pi) + delta)
    let high := base.filter (fun n =>
      (k : Real) * (2 * Real.pi) + (2 * Real.pi - delta) <= theta n ∧
        theta n <= ((k : Real) + 1) * (2 * Real.pi))
    have hsplit :
        (∑ n ∈ fiber k, unitaryPhase (f n)) =
          (∑ n ∈ base.filter (good k), unitaryPhase (f n)) +
            ∑ n ∈ bad, unitaryPhase (f n) := by
      have hraw := Finset.sum_filter_add_sum_filter_not
        (s := fiber k) (p := good k) (f := fun n => unitaryPhase (f n))
      rw [← hraw]
      congr 2
      ext n
      constructor
      · intro hn
        have hnData := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hnData.1).1, hnData.2⟩
      · intro hn
        have hnData := Finset.mem_filter.mp hn
        exact Finset.mem_filter.mpr ⟨hgood_subset k hn, hnData.2⟩
    have hbad_subset : bad ⊆ low ∪ high := by
      intro n hn
      have hnData := Finset.mem_filter.mp hn
      have hfibData := Finset.mem_filter.mp hnData.1
      have hperiod := periodIndex_bounds (theta n)
      have hidx : periodIndex (theta n) = k := hfibData.2
      rw [hidx] at hperiod
      have hnot := hnData.2
      simp only [good, not_and_or, not_le] at hnot
      apply Finset.mem_union.mpr
      rcases hnot with hlow | hhigh
      · left
        apply Finset.mem_filter.mpr
        exact ⟨hfibData.1, ⟨hperiod.1, by linarith⟩⟩
      · right
        apply Finset.mem_filter.mpr
        exact ⟨hfibData.1, ⟨by linarith, hperiod.2.le⟩⟩
    have hbad_card_nat : bad.card <= low.card + high.card :=
      (Finset.card_le_card hbad_subset).trans (Finset.card_union_le low high)
    have hlow_card : (low.card : Real) <= delta / lambda + 1 := by
      simpa only [low, add_sub_cancel_left] using
        filter_card_bound theta N lambda
          ((k : Real) * (2 * Real.pi))
          ((k : Real) * (2 * Real.pi) + delta) hlambda (by linarith [hdelta])
          (fun n hn => by dsimp only [theta]; exact hlower n hn)
    have hhigh_card : (high.card : Real) <= delta / lambda + 1 := by
      have heq : ((k : Real) + 1) * (2 * Real.pi) -
          ((k : Real) * (2 * Real.pi) + (2 * Real.pi - delta)) = delta := by ring
      have hbaseCard := filter_card_bound theta N lambda
        ((k : Real) * (2 * Real.pi) + (2 * Real.pi - delta))
        (((k : Real) + 1) * (2 * Real.pi)) hlambda
        (by linarith [hdelta])
        (fun n hn => by dsimp only [theta]; exact hlower n hn)
      simpa only [high, heq] using hbaseCard
    have hbad_card : (bad.card : Real) <= 2 * (delta / lambda + 1) := by
      have hcast : (bad.card : Real) <= (low.card : Real) + (high.card : Real) := by
        exact_mod_cast hbad_card_nat
      linarith
    have hgood_bound :
        ‖∑ n ∈ base.filter (good k), unitaryPhase (f n)‖ <= 2 * Real.pi / delta := by
      simpa only [base, good, theta] using
        kusminLandau_good_fiber f N k delta hdelta
          (fun n hn => by linarith [hlower n hn])
    rw [hsplit]
    calc
      ‖(∑ n ∈ base.filter (good k), unitaryPhase (f n)) +
          ∑ n ∈ bad, unitaryPhase (f n)‖ <=
          ‖∑ n ∈ base.filter (good k), unitaryPhase (f n)‖ +
            ‖∑ n ∈ bad, unitaryPhase (f n)‖ := norm_add_le _ _
      _ <= 2 * Real.pi / delta + 2 * (delta / lambda + 1) := by
        exact add_le_add hgood_bound ((norm_phase_sum_finset_le_card bad f).trans hbad_card)
  rw [← hpartition]
  calc
    ‖∑ k ∈ K, ∑ n ∈ fiber k, unitaryPhase (f n)‖ <=
        ∑ k ∈ K, ‖∑ n ∈ fiber k, unitaryPhase (f n)‖ := norm_sum_le _ _
    _ <= ∑ _k ∈ K, (2 * Real.pi / delta + 2 * (delta / lambda + 1)) := by
      exact Finset.sum_le_sum fun k hk => hfiber k hk
    _ = (K.card : Real) * (2 * Real.pi / delta + 2 * (delta / lambda + 1)) := by
      simp
      ring
    _ <= ((N : Real) * Lambda / (2 * Real.pi) + 2) *
        (2 * Real.pi / delta + 2 * (delta / lambda + 1)) := by
      have htheta : theta N - theta 0 <= (N : Real) * Lambda := by
        simpa only [Nat.zero_add] using
          discrete_growth_upper theta Lambda 0 N N
            (fun n hn => by dsimp only [theta]; exact hupper n hn) (by omega)
      have hperiods := period_count_bound (hmono 0 N (by omega) le_rfl)
      have hK : (K.card : Real) <= (N : Real) * Lambda / (2 * Real.pi) + 2 := by
        dsimp only [K, idx]
        calc
          ((Finset.Icc (periodIndex (theta 0))
              (periodIndex (theta N))).card : Real) <=
              (theta N - theta 0) / (2 * Real.pi) + 2 := hperiods
          _ <= (N : Real) * Lambda / (2 * Real.pi) + 2 := by
            gcongr
      exact mul_le_mul_of_nonneg_right hK (by positivity)

/-- The optimized B-process: choosing the endpoint width `sqrt lambda`
exhibits the classical `(1/2, 1/2)` second-derivative scale.  The displayed
formula keeps the constants and the upper/lower curvature ratio explicit. -/
theorem vanDerCorput_B_process
    (f : Nat -> Real) (N : Nat) (lambda Lambda : Real)
    (hlambda : 0 < lambda)
    (hlower : forall n, n < N ->
      lambda <= (f (n + 2) - f (n + 1)) - (f (n + 1) - f n))
    (hupper : forall n, n < N ->
      (f (n + 2) - f (n + 1)) - (f (n + 1) - f n) <= Lambda) :
    ‖∑ n ∈ Finset.range (N + 1), unitaryPhase (f n)‖ <=
      ((N : Real) * Lambda / (2 * Real.pi) + 2) *
        (2 * Real.pi / Real.sqrt lambda +
          2 * (Real.sqrt lambda / lambda + 1)) := by
  exact vanDerCorput_second_derivative f N lambda Lambda (Real.sqrt lambda)
    hlambda (Real.sqrt_pos.2 hlambda) hlower hupper

end RiemannZeta.GuthMaynard
