module
public import MathCollab.Density.LargeValueDefinitions
public import Mathlib.Analysis.PSeries

@[expose] public section

open Real Set MeasureTheory
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

theorem intervalSpan_nonneg (U : Finset ℝ) : 0 ≤ intervalSpan U := by
  by_cases hU : U.Nonempty
  · simp only [intervalSpan, dite_eq_left hU]
    exact sub_nonneg.mpr (U.min'_le _ (U.max'_mem hU))
  · simp only [intervalSpan, dite_eq_right hU, le_refl]

theorem localDiameter_ge_one (U : Finset ℝ) : 1 ≤ localDiameter U := by
  have := intervalSpan_nonneg U
  dsimp [localDiameter]
  linarith

theorem abs_sub_le_intervalSpan {U : Finset ℝ} {t u : ℝ} (ht : t ∈ U) (hu : u ∈ U) :
    |t-u| ≤ intervalSpan U := by
  have hU : U.Nonempty := ⟨t, ht⟩
  simp only [intervalSpan, dite_eq_left hU]
  have htlo := U.min'_le t ht
  have hthi := U.le_max' t ht
  have hulo := U.min'_le u hu
  have huhi := U.le_max' u hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem intervalSpan_le_of_forall {U : Finset ℝ} {D : ℝ} (hD : 0 ≤ D)
    (h : ∀ t ∈ U, ∀ u ∈ U, |t-u| ≤ D) : intervalSpan U ≤ D := by
  by_cases hU : U.Nonempty
  · simp only [intervalSpan, dite_eq_left hU]
    exact (le_abs_self _).trans (h _ (U.max'_mem hU) _ (U.min'_mem hU))
  · simpa only [intervalSpan, dite_eq_right hU] using hD

theorem separated_floor_shift_injOn {U : Finset ℝ} (hU : oneSeparated U) (s : ℝ) :
    Set.InjOn (fun t : ℝ => ⌊t-s⌋) (U : Set ℝ) := by
  intro t ht u hu he
  by_contra hne
  have hs := hU t ht u hu hne
  have htlo := Int.floor_le (t-s)
  have hthi := Int.lt_floor_add_one (t-s)
  have hulo := Int.floor_le (u-s)
  have huhi := Int.lt_floor_add_one (u-s)
  change ⌊t-s⌋ = ⌊u-s⌋ at he
  rw [he] at htlo hthi
  have hd : |t-u| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
  linarith

/-- Exact packing without an additional cardinality factor. -/
theorem separated_card_le_localDiameter {U : Finset ℝ} (hsep : oneSeparated U) :
    (U.card : ℝ) ≤ localDiameter U := by
  by_cases hU : U.Nonempty
  · let a := U.min' hU
    let D := U.max' hU - a
    have hD : 0 ≤ D := sub_nonneg.mpr (U.min'_le _ (U.max'_mem hU))
    have hf : (0 : ℤ) ≤ ⌊D⌋ := Int.le_floor.mpr (by exact_mod_cast hD)
    have hmap : Set.MapsTo (fun t : ℝ => ⌊t-a⌋) (U : Set ℝ) (Finset.Icc (0 : ℤ) ⌊D⌋) := by
      intro t ht
      apply Finset.mem_Icc.mpr
      constructor
      · apply Int.le_floor.mpr
        have hh := U.min'_le t ht
        simp only [Int.cast_zero]
        exact sub_nonneg.mpr hh
      · exact Int.floor_mono (sub_le_sub_right (U.le_max' t ht) a)
    have hc := Finset.card_le_card_of_injOn (fun t : ℝ => ⌊t-a⌋) hmap
      (separated_floor_shift_injOn hsep a)
    have hcR : (U.card : ℝ) ≤ ((Finset.Icc (0 : ℤ) ⌊D⌋).card : ℝ) := by exact_mod_cast hc
    have he : (((Finset.Icc (0 : ℤ) ⌊D⌋).card : ℕ) : ℝ) = (⌊D⌋ : ℝ)+1 := by
      rw [Int.card_Icc]
      simp only [sub_zero]
      have hi := Int.toNat_of_nonneg (show 0 ≤ ⌊D⌋ + 1 by omega)
      exact_mod_cast hi
    rw [he] at hcR
    change (U.card : ℝ) ≤ 1 + intervalSpan U
    simp only [intervalSpan, dite_eq_left hU]
    have hfloor := Int.floor_le D
    dsimp [D, a] at hcR hfloor
    linarith
  · have he := Finset.not_nonempty_iff_eq_empty.mp hU
    subst U
    simp [localDiameter, intervalSpan]

/-- A single absolute constant for every separated row. -/
def separationMass : ℝ := ∑' z : ℤ, 4/(1+|(z : ℝ)|)^2

theorem summable_separation_majorant : Summable (fun z : ℤ => 4/(1+|(z : ℝ)|)^2) := by
  have hn : Summable (fun n : ℕ => 1/((n : ℝ)+1)^2) := by
    have hh := (summable_nat_add_iff 1).2
      ((Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num))
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hi : Summable (fun z : ℤ => 1/(1+|(z : ℝ)|)^2) := by
    apply Summable.of_nat_of_neg
    · simpa only [Int.cast_natCast, Nat.abs_cast, add_comm] using hn
    · simpa only [Int.cast_neg, abs_neg, Int.cast_natCast,
        Nat.abs_cast, add_comm] using hn
  simpa only [← mul_div_assoc, mul_one] using hi.mul_left 4

theorem separationMass_nonneg : 0 ≤ separationMass :=
  tsum_nonneg (fun _ => by positivity)

theorem decay_le_floor_majorant (x : ℝ) :
    1/(1+|x|)^2 ≤ 4/(1+|(⌊x⌋ : ℝ)|)^2 := by
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  have hf : |(⌊x⌋ : ℝ)| ≤ |x|+1 := abs_le.mpr
    ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hp : (1+|(⌊x⌋ : ℝ)|)^2 ≤ 4*(1+|x|)^2 := by
    have ha := abs_nonneg x
    have hb := abs_nonneg (⌊x⌋ : ℝ)
    nlinarith
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (1+|x|)^2)
    (by positivity : (0 : ℝ) < (1+|(⌊x⌋ : ℝ)|)^2)).2
  simpa only [one_mul] using hp

theorem separated_decay_row {U : Finset ℝ} (hsep : oneSeparated U) (t : ℝ) :
    (∑ u ∈ U, 1/(1+|t-u|)^2) ≤ separationMass := by
  let f : ℝ → ℤ := fun u => ⌊u-t⌋
  calc
    _ = ∑ u ∈ U, 1/(1+|u-t|)^2 := by simp only [abs_sub_comm]
    _ ≤ ∑ u ∈ U, 4/(1+|(f u : ℝ)|)^2 :=
      Finset.sum_le_sum (fun u _ => decay_le_floor_majorant (u-t))
    _ = ∑ z ∈ U.image f, 4/(1+|(z : ℝ)|)^2 :=
      (Finset.sum_image (f := fun z : ℤ => 4/(1+|(z : ℝ)|)^2)
        (separated_floor_shift_injOn hsep t)).symm
    _ ≤ separationMass := summable_separation_majorant.sum_le_tsum _ (fun _ _ => by positivity)

theorem separated_decay_pairs {U : Finset ℝ} (hsep : oneSeparated U) :
    (∑ t ∈ U, ∑ u ∈ U, 1/(1+|t-u|)^2) ≤ separationMass * U.card := by
  calc
    _ ≤ ∑ _t ∈ U, separationMass := Finset.sum_le_sum (fun t _ => separated_decay_row hsep t)
    _ = _ := by simp [mul_comm]

theorem LargeValueData.local_card_le {κ : ℝ} (d : LargeValueData κ) {U : Finset ℝ}
    (hU : U ⊆ d.W) : (U.card : ℝ) ≤ localDiameter U ∧ localDiameter U ≤ d.T+1 := by
  refine ⟨separated_card_le_localDiameter (oneSeparated_subset d.separated hU), ?_⟩
  have hs : intervalSpan U ≤ d.T := by
    apply intervalSpan_le_of_forall (by linarith [d.T_ge_two])
    intro t ht u hu
    have hh := d.location t (hU ht)
    have hi := d.location u (hU hu)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  dsimp [localDiameter]
  linarith

end MathCollab.Density
