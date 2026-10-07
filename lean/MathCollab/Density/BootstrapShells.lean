module
public import MathCollab.Density.BootstrapShell

@[expose] public section

open Real Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

def shellIndices (U : Finset ℝ) : Finset ℕ :=
  (Finset.range (⌊intervalSpan U⌋₊.log2+1)).filter (fun k => (2 : ℝ)^k ≤ intervalSpan U)

theorem shellIndex_bounds {U : Finset ℝ} {k : ℕ} (hk : k ∈ shellIndices U) :
    1 ≤ (2 : ℝ)^k ∧ (2 : ℝ)^k ≤ intervalSpan U :=
  ⟨one_le_pow₀ (by norm_num), (Finset.mem_filter.mp hk).2⟩

theorem exists_shellIndex {U : Finset ℝ} {x : ℝ} (hx : 1 ≤ x) (hxU : x ≤ intervalSpan U) :
    ∃ k ∈ shellIndices U, (2 : ℝ)^k ≤ x ∧ x < 2*(2 : ℝ)^k := by
  have hxp : 0 < ⌊x⌋₊ := (Nat.one_le_floor_iff x).2 hx
  have hDp : 0 < ⌊intervalSpan U⌋₊ := (Nat.one_le_floor_iff _).2 (hx.trans hxU)
  have hb := log2_block_bounds hxp
  have hlow : (2 : ℝ)^⌊x⌋₊.log2 ≤ x := by
    have hh : (2 : ℝ)^⌊x⌋₊.log2 ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast hb.1
    exact hh.trans (Nat.floor_le (by linarith))
  refine ⟨⌊x⌋₊.log2, ?_, hlow, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hlow.trans hxU⟩
    have hh := (Nat.le_log2 hDp.ne').2 (hb.1.trans (Nat.floor_mono hxU))
    omega
  · have hi : (⌊x⌋₊ : ℝ)+1 ≤ 2*(2 : ℝ)^⌊x⌋₊.log2 := by exact_mod_cast hb.2
    exact (Nat.lt_floor_add_one x).trans_le hi

theorem shellIndices_sum_le (U : Finset ℝ) :
    (∑ k ∈ shellIndices U, (2 : ℝ)^k) ≤ 2*localDiameter U := by
  let n := ⌊intervalSpan U⌋₊
  have hn : (n : ℝ) ≤ intervalSpan U := Nat.floor_le (intervalSpan_nonneg U)
  have hpow : (2 : ℝ)^n.log2 ≤ localDiameter U := by
    by_cases hp : 0 < n
    · have hh : (2 : ℝ)^n.log2 ≤ n := by exact_mod_cast (log2_block_bounds hp).1
      have hd := intervalSpan_nonneg U
      dsimp [localDiameter]
      linarith
    · have hz : n = 0 := by omega
      simpa only [hz, Nat.log2_zero, pow_zero] using localDiameter_ge_one U
  calc
    _ ≤ ∑ k ∈ Finset.range (n.log2+1), (2 : ℝ)^k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = (2 : ℝ)^(n.log2+1)-1 := by rw [geom_sum_eq (by norm_num)]; norm_num
    _ ≤ _ := by rw [pow_succ]; linarith

theorem shellIndices_card_le_log {U : Finset ℝ} {T : ℝ} (hT : 2 ≤ T)
    (hD : intervalSpan U ≤ T) :
    ((shellIndices U).card : ℝ) ≤ Real.log (2*T)/Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hD1 : 1 ≤ intervalSpan U
  · let n := ⌊intervalSpan U⌋₊
    have hnp : 0 < n := (Nat.one_le_floor_iff _).2 hD1
    have hn : (n : ℝ) ≤ intervalSpan U := Nat.floor_le (intervalSpan_nonneg U)
    have hp : (2 : ℝ)^n.log2 ≤ n := by exact_mod_cast (log2_block_bounds hnp).1
    have he : (2 : ℝ)^(n.log2+1) ≤ 2*T := by rw [pow_succ]; nlinarith
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ)^(n.log2+1)) he
    rw [Real.log_pow] at hh
    have hc : ((shellIndices U).card : ℝ) ≤ (n.log2+1 : ℕ) := by
      have hcNat : (shellIndices U).card ≤ n.log2+1 :=
        (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
      exact_mod_cast hcNat
    exact hc.trans ((le_div_iff₀ hlog).2 hh)
  · have he : shellIndices U = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      exact hD1 ((shellIndex_bounds hk).1.trans (shellIndex_bounds hk).2)
    rw [he, Finset.card_empty, Nat.cast_zero]
    exact div_nonneg (Real.log_nonneg (by linarith)) hlog.le

theorem shellIndices_card_le_diameter (U : Finset ℝ) :
    ((shellIndices U).card : ℝ) ≤ localDiameter U := by
  have hc : (shellIndices U).card ≤ ⌊intervalSpan U⌋₊+1 :=
    (Finset.card_filter_le _ _).trans ((Finset.card_range _).le.trans
      (Nat.add_le_add_right (Nat.log2_le_self _) 1))
  have hcR : ((shellIndices U).card : ℝ) ≤ (⌊intervalSpan U⌋₊ : ℝ)+1 := by exact_mod_cast hc
  have hf := Nat.floor_le (intervalSpan_nonneg U)
  dsimp [localDiameter]
  linarith

theorem shellEnergy_nonneg (w : ReflectionCutoff) (L H : ℝ) (U : Finset ℝ) :
    0 ≤ shellEnergy w L H U := by
  apply Finset.sum_nonneg
  intro t ht
  apply Finset.sum_nonneg
  intro u hu
  split_ifs <;> positivity

/-- Each off-diagonal pair lies in an actual dyadic shell with H at most its diameter. -/
theorem kernelEnergy_le_dyadic_shells (w : ReflectionCutoff) (L : ℝ)
    {U : Finset ℝ} (hsep : oneSeparated U) :
    kernelEnergy w L U ≤ (∑ _t ∈ U, ‖hKernel w L 0‖^2) +
      ∑ k ∈ shellIndices U, shellEnergy w L ((2 : ℝ)^k) U := by
  have hp (t u : ℝ) (ht : t ∈ U) (hu : u ∈ U) :
      ‖hKernel w L (t-u)‖^2 ≤ (if t=u then ‖hKernel w L 0‖^2 else 0) +
        ∑ k ∈ shellIndices U, if (2 : ℝ)^k ≤ |t-u| ∧ |t-u| < 2*(2 : ℝ)^k then
          ‖hKernel w L (t-u)‖^2 else 0 := by
    by_cases he : t=u
    · subst u
      simp only [sub_self]
      exact le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))
    · rw [ite_eq_right he, zero_add]
      obtain ⟨k, hk, hdist⟩ := exists_shellIndex (hsep t ht u hu he) (abs_sub_le_intervalSpan ht hu)
      have hh := Finset.single_le_sum (s := shellIndices U)
        (f := fun k => if (2 : ℝ)^k ≤ |t-u| ∧ |t-u| < 2*(2 : ℝ)^k then
          ‖hKernel w L (t-u)‖^2 else 0)
        (fun _ _ => by split_ifs <;> positivity) hk
      simpa only [ite_eq_left hdist] using hh
  calc
    _ ≤ ∑ t ∈ U, ∑ u ∈ U,
        ((if t=u then ‖hKernel w L 0‖^2 else 0) +
          ∑ k ∈ shellIndices U, if (2 : ℝ)^k ≤ |t-u| ∧ |t-u| < 2*(2 : ℝ)^k then
            ‖hKernel w L (t-u)‖^2 else 0) :=
      Finset.sum_le_sum (fun t ht => Finset.sum_le_sum (fun u hu => hp t u ht hu))
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        simp [ht]
      · simp_rw [Finset.sum_comm (s := U) (t := shellIndices U)]
        rfl

end MathCollab.Density
