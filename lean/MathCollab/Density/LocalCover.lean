module
public import MathCollab.Density.CompletePairs

@[expose] public section

open Real Complex Set
open scoped BigOperators

noncomputable section
namespace MathCollab.Density

def localIndices (U : Finset ℝ) (H : ℝ) : Finset ℤ :=
  U.biUnion (fun t => Finset.Icc (⌊t/H⌋-2) ⌊t/H⌋)

theorem mem_localSet_iff_floor {U : Finset ℝ} {H t : ℝ} (hH : 0 < H) (j : ℤ) :
    t ∈ localSet U H j ↔ t ∈ U ∧ ⌊t/H⌋-2 ≤ j ∧ j ≤ ⌊t/H⌋ := by
  simp only [localSet, Finset.mem_filter]
  constructor
  · rintro ⟨ht, hlo, hhi⟩
    have hj : (j : ℝ) ≤ t/H := (le_div_iff₀ hH).2 hlo
    have hj' : t/H < (j : ℝ)+3 := (div_lt_iff₀ hH).2 hhi
    have hf := Int.floor_le (t/H)
    have hfloor : ⌊t/H⌋ < j+3 := by exact_mod_cast (hf.trans_lt hj')
    exact ⟨ht, by omega, Int.le_floor.mpr hj⟩
  · rintro ⟨ht, hlo, hhi⟩
    refine ⟨ht, ?_, ?_⟩
    · apply (le_div_iff₀ hH).1
      exact (Int.cast_le.mpr hhi).trans (Int.floor_le (t/H))
    · apply (div_lt_iff₀ hH).1
      have hf := Int.lt_floor_add_one (t/H)
      have hh : ((⌊t/H⌋ : ℤ) : ℝ) + 1 ≤ (j : ℝ)+3 := by exact_mod_cast (show ⌊t/H⌋+1 ≤ j+3 by omega)
      exact hf.trans_le hh

theorem mem_localIndices_iff {U : Finset ℝ} {H : ℝ} (hH : 0 < H) (j : ℤ) :
    j ∈ localIndices U H ↔ ∃ t ∈ U, t ∈ localSet U H j := by
  simp only [localIndices, Finset.mem_biUnion, Finset.mem_Icc]
  constructor
  · rintro ⟨t, ht, hj⟩
    exact ⟨t, ht, (mem_localSet_iff_floor hH j).2 ⟨ht, hj⟩⟩
  · rintro ⟨t, ht, hj⟩
    exact ⟨t, ht, ((mem_localSet_iff_floor hH j).1 hj).2⟩

theorem localSet_eq_empty_of_notMem {U : Finset ℝ} {H : ℝ} (hH : 0 < H)
    {j : ℤ} (hj : j ∉ localIndices U H) : localSet U H j = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact hj ((mem_localIndices_iff hH j).2 ⟨t, (Finset.mem_filter.mp ht).1, ht⟩)

/-- Every pair at distance less than 2H lies in one complete local pair set. -/
theorem pair_mem_localSet {U : Finset ℝ} {H t u : ℝ} (hH : 0 < H)
    (ht : t ∈ U) (hu : u ∈ U) (hclose : |t-u| < 2*H) :
    ∃ j ∈ localIndices U H, t ∈ localSet U H j ∧ u ∈ localSet U H j := by
  let j : ℤ := ⌊min t u / H⌋
  have hlo : (j : ℝ)*H ≤ min t u := (le_div_iff₀ hH).1 (Int.floor_le _)
  have hhi : min t u < ((j : ℝ)+1)*H := (div_lt_iff₀ hH).1 (Int.lt_floor_add_one _)
  have hdist := abs_lt.mp hclose
  have htj : t ∈ localSet U H j := by
    apply Finset.mem_filter.mpr
    refine ⟨ht, hlo.trans (min_le_left _ _), ?_⟩
    rcases le_total t u with htu | hut
    · rw [min_eq_left htu] at hhi
      nlinarith
    · rw [min_eq_right hut] at hhi
      nlinarith [hdist.2]
  have huj : u ∈ localSet U H j := by
    apply Finset.mem_filter.mpr
    refine ⟨hu, hlo.trans (min_le_right _ _), ?_⟩
    rcases le_total t u with htu | hut
    · rw [min_eq_left htu] at hhi
      nlinarith [hdist.1]
    · rw [min_eq_right hut] at hhi
      nlinarith
  exact ⟨j, (mem_localIndices_iff hH j).2 ⟨t, ht, htj⟩, htj, huj⟩

/-- Extending a complete pair sum to an ambient finite set with zero indicators. -/
theorem sum_pairs_indicator {E : Type*} [AddCommMonoid E] {U V : Finset ℝ}
    (hVU : V ⊆ U) (F : ℝ → ℝ → E) :
    (∑ t ∈ U, ∑ u ∈ U, if t ∈ V ∧ u ∈ V then F t u else 0) =
      ∑ t ∈ V, ∑ u ∈ V, F t u := by
  have he : U.filter (fun t => t ∈ V) = V := by
    ext t
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hVU h, h⟩⟩
  conv_rhs => rw [← he]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : t ∈ V <;> simp [ht]

/-- A shell may be enlarged to complete local pairs before coefficient domination. -/
theorem close_pairs_le_local_pairs {U : Finset ℝ} {H : ℝ} (hH : 0 < H)
    (F : ℝ → ℝ → ℝ) (hF : ∀ t u, 0 ≤ F t u) :
    (∑ t ∈ U, ∑ u ∈ U, if |t-u| < 2*H then F t u else 0) ≤
      ∑ j ∈ localIndices U H, ∑ t ∈ localSet U H j, ∑ u ∈ localSet U H j, F t u := by
  calc
    _ ≤ ∑ t ∈ U, ∑ u ∈ U, ∑ j ∈ localIndices U H,
        if t ∈ localSet U H j ∧ u ∈ localSet U H j then F t u else 0 := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      by_cases hc : |t-u| < 2*H
      · obtain ⟨j, hj, htj, huj⟩ := pair_mem_localSet hH ht hu hc
        rw [ite_eq_left hc]
        have hh := Finset.single_le_sum (s := localIndices U H)
          (f := fun j => if t ∈ localSet U H j ∧ u ∈ localSet U H j then F t u else 0)
          (fun j _ => by split_ifs <;> first | exact hF t u | exact le_rfl) hj
        simpa only [htj, huj, and_self, ↓reduceIte] using hh
      · rw [ite_eq_right hc]
        exact Finset.sum_nonneg (fun j _ => by split_ifs <;> first | exact hF t u | exact le_rfl)
    _ = ∑ j ∈ localIndices U H, ∑ t ∈ U, ∑ u ∈ U,
        if t ∈ localSet U H j ∧ u ∈ localSet U H j then F t u else 0 := by
      simp_rw [Finset.sum_comm (s := U) (t := localIndices U H)]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_pairs_indicator (Finset.filter_subset _ _) F

theorem tsum_completePairEnergy_localSet {U : Finset ℝ} {H : ℝ} (hH : 0 < H) (M : ℕ) :
    (∑' j : ℤ, completePairEnergy M (localSet U H j)) =
      ∑ j ∈ localIndices U H, completePairEnergy M (localSet U H j) := by
  apply tsum_eq_sum
  intro j hj
  simp only [localSet_eq_empty_of_notMem hH hj, completePairEnergy, Finset.sum_empty]

/-- Each original point belongs to exactly three consecutive local sets. -/
theorem localIndices_filter_point {U : Finset ℝ} {H t : ℝ} (hH : 0 < H) (ht : t ∈ U) :
    (localIndices U H).filter (fun j => t ∈ localSet U H j) =
      Finset.Icc (⌊t/H⌋-2) ⌊t/H⌋ := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro hh
    exact ((mem_localSet_iff_floor hH j).1 hh.2).2
  · intro hj
    have hmem := (mem_localSet_iff_floor hH j).2 ⟨ht, hj⟩
    exact ⟨(mem_localIndices_iff hH j).2 ⟨t, ht, hmem⟩, hmem⟩

theorem sum_card_localSet {U : Finset ℝ} {H : ℝ} (hH : 0 < H) :
    (∑ j ∈ localIndices U H, (localSet U H j).card) = 3*U.card := by
  have he (j : ℤ) : (localSet U H j).card = ∑ t ∈ U, if t ∈ localSet U H j then 1 else 0 := by
    rw [← Finset.sum_filter]
    have hh : U.filter (fun t => t ∈ localSet U H j) = localSet U H j := by
      ext t
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨(Finset.mem_filter.mp h).1, h⟩⟩
    rw [hh]
    simp
  simp_rw [he]
  rw [Finset.sum_comm]
  calc
    _ = ∑ t ∈ U, 3 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [← Finset.sum_filter, localIndices_filter_point hH ht]
      simp
    _ = _ := by simp only [Finset.sum_const, smul_eq_mul]; omega

theorem tsum_card_localSet {U : Finset ℝ} {H : ℝ} (hH : 0 < H) :
    (∑' j : ℤ, ((localSet U H j).card : ℝ)) = 3*(U.card : ℝ) := by
  rw [tsum_eq_sum (s := localIndices U H) (fun j hj => by
    simp only [localSet_eq_empty_of_notMem hH hj, Finset.card_empty, Nat.cast_zero])]
  exact_mod_cast sum_card_localSet (U := U) hH

/-- The local interval has diameter at most 3H, with no separation premise. -/
theorem localSet_pair_distance {U : Finset ℝ} {H : ℝ} {j : ℤ} {t u : ℝ}
    (ht : t ∈ localSet U H j) (hu : u ∈ localSet U H j) : |t-u| < 3*H := by
  have htt := (Finset.mem_filter.mp ht).2
  have huu := (Finset.mem_filter.mp hu).2
  apply abs_lt.mpr
  constructor <;> nlinarith [htt.1, htt.2, huu.1, huu.2]

end MathCollab.Density
