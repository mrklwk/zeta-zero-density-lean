module
public import MathCollab.Density.ZetaCounting
public import MathCollab.Density.LargeValueDefinitions

@[expose] public section

open Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- Unit bins are half open: an integer ordinate belongs to the bin starting there. -/
def ordinateBin (ρ : ℂ) : ℤ := ⌊ρ.im⌋

theorem ordinateBin_eq_iff {ρ : ℂ} {k : ℤ} :
    ordinateBin ρ = k ↔ (k : ℝ) ≤ ρ.im ∧ ρ.im < (k : ℝ)+1 := by
  exact Int.floor_eq_iff

/-- Half the occupied bins have a common parity, including for negative indices. -/
theorem occupied_bins_parity (K : Finset ℤ) :
    ∃ J : Finset ℤ, J ⊆ K ∧ K.card ≤ 2*J.card ∧
      ∀ k ∈ J, ∀ l ∈ J, k % 2 = l % 2 := by
  classical
  let A := K.filter (fun k => k % 2 = 0)
  let B := K.filter (fun k => ¬k % 2 = 0)
  have hc : A.card+B.card = K.card := Finset.card_filter_add_card_filter_not _
  by_cases h : B.card ≤ A.card
  · refine ⟨A, Finset.filter_subset _ _, by omega, ?_⟩
    intro k hk l hl
    exact (Finset.mem_filter.mp hk).2.trans (Finset.mem_filter.mp hl).2.symm
  · refine ⟨B, Finset.filter_subset _ _, by omega, ?_⟩
    intro k hk l hl
    have hk' := (Finset.mem_filter.mp hk).2
    have hl' := (Finset.mem_filter.mp hl).2
    omega

theorem same_parity_bins_separated {x y : ℝ} (hne : ⌊x⌋ ≠ ⌊y⌋)
    (hpar : ⌊x⌋ % 2 = ⌊y⌋ % 2) : 1 ≤ |x-y| := by
  have hxlo := Int.floor_le x
  have hxhi := Int.lt_floor_add_one x
  have hylo := Int.floor_le y
  have hyhi := Int.lt_floor_add_one y
  rcases lt_or_gt_of_ne hne with h | h
  · have hi : ⌊x⌋+2 ≤ ⌊y⌋ := by omega
    have hr : (⌊x⌋ : ℝ)+2 ≤ (⌊y⌋ : ℝ) := by exact_mod_cast hi
    have := neg_le_abs (x-y)
    linarith
  · have hi : ⌊y⌋+2 ≤ ⌊x⌋ := by omega
    have hr : (⌊y⌋ : ℝ)+2 ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hi
    have := le_abs_self (x-y)
    linarith

/-- A finite weighted set of actual locations has separated representatives.
The explicit bin bound is where a later local zero-count estimate must enter. -/
theorem weighted_separated_extraction (S : Finset ℂ) (w : ℂ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hbin : ∀ k : ℤ, (∑ ρ ∈ S with ordinateBin ρ = k, w ρ) ≤ B) :
    ∃ R : Finset ℂ, R ⊆ S ∧ (R.image Complex.im).card = R.card ∧
      oneSeparated (R.image Complex.im) ∧ (∑ ρ ∈ S, w ρ) ≤ 2*B*(R.card : ℝ) := by
  classical
  let K := S.image ordinateBin
  obtain ⟨J, hJK, hcard, hpar⟩ := occupied_bins_parity K
  have hex : ∀ k : ℤ, ∃ ρ : ℂ, k ∈ K → ρ ∈ S ∧ ordinateBin ρ = k := by
    intro k
    by_cases hk : k ∈ K
    · obtain ⟨ρ, hρ, he⟩ := Finset.mem_image.mp hk
      exact ⟨ρ, fun _ => ⟨hρ, he⟩⟩
    · exact ⟨0, fun h => (hk h).elim⟩
  choose f hf using hex
  have hfJ : ∀ k ∈ J, f k ∈ S ∧ ordinateBin (f k) = k := fun k hk => hf k (hJK hk)
  have hinj : Set.InjOn f (J : Set ℤ) := by
    intro k hk l hl he
    calc
      k = ordinateBin (f k) := (hfJ k hk).2.symm
      _ = ordinateBin (f l) := congrArg ordinateBin he
      _ = l := (hfJ l hl).2
  have himinj : Set.InjOn Complex.im ((J.image f) : Set ℂ) := by
    intro ρ hρ ω hω he
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hω
    have hkl : k = l := by
      rw [← (hfJ k hk).2, ← (hfJ l hl).2]
      exact congrArg Int.floor he
    rw [hkl]
  refine ⟨J.image f, ?_, Finset.card_image_of_injOn himinj, ?_, ?_⟩
  · intro ρ hρ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hρ
    exact (hfJ k hk).1
  · intro x hx y hy hxy
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨ω, hω, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hρ
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hω
    apply same_parity_bins_separated
    · change ordinateBin (f k) ≠ ordinateBin (f l)
      rw [(hfJ k hk).2, (hfJ l hl).2]
      intro he
      exact hxy (congrArg (fun i => (f i).im) he)
    · change ordinateBin (f k) % 2 = ordinateBin (f l) % 2
      rw [(hfJ k hk).2, (hfJ l hl).2]
      exact hpar k hk l hl
  · rw [Finset.card_image_of_injOn hinj]
    have hsum : (∑ ρ ∈ S, w ρ) ≤ (K.card : ℝ)*B := by
      rw [← Finset.sum_fiberwise_of_maps_to
        (fun ρ hρ => Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩ : ∀ ρ ∈ S, ordinateBin ρ ∈ K) w]
      calc
        _ ≤ ∑ _k ∈ K, B := Finset.sum_le_sum fun k _ => hbin k
        _ = (K.card : ℝ)*B := by simp
    have hc : (K.card : ℝ) ≤ 2*(J.card : ℝ) := by exact_mod_cast hcard
    nlinarith

/-- This is a conditional use of a local multiplicity estimate, not that estimate. -/
theorem zetaSlab_separated_representatives (σ a b : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ k : ℤ,
      (∑ ρ ∈ (zetaZeroFinset σ a b).filter (fun ρ => ordinateBin ρ = k),
        (zetaMultiplicity ρ : ℝ)) ≤ B) :
    ∃ R : Finset ℂ, R ⊆ zetaZeroFinset σ a b ∧
      (R.image Complex.im).card = R.card ∧ oneSeparated (R.image Complex.im) ∧
      (zetaSlabCount σ a b : ℝ) ≤ 2*B*(R.card : ℝ) := by
  simpa only [zetaSlabCount, Nat.cast_sum] using
    weighted_separated_extraction (zetaZeroFinset σ a b) (fun ρ => (zetaMultiplicity ρ : ℝ))
      hB hlocal

end MathCollab.Density
