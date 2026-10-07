module
public import MathCollab.Density.ComparisonCutoff

@[expose] public section

open Real Complex Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

def productPairs (N M : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ioc N (2*N)) ×ˢ (Finset.Ico M (2*M))

def productMultiplicity (N M m : ℕ) : ℕ :=
  ((productPairs N M).filter (fun p => p.1*p.2=m)).card

theorem productMultiplicity_le_divisors {N M m : ℕ} (hm : m ≠ 0) :
    productMultiplicity N M m ≤ m.divisors.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    exact Nat.mem_divisors.mpr ⟨⟨p.2, hp'.2.symm⟩, hm⟩
  · intro p hp q hq he
    have hp' := Finset.mem_filter.mp hp
    have hq' := Finset.mem_filter.mp hq
    have hn : 0 < p.1 := by
      have hh := (Finset.mem_Ioc.mp (Finset.mem_product.mp hp'.1).1).1
      omega
    apply Prod.ext he
    have hh : p.1*p.2 = p.1*q.2 := by rw [hp'.2, he, hq'.2]
    exact Nat.eq_of_mul_eq_mul_left hn hh

theorem product_range {N M : ℕ} (_hN : 0 < N) (hM : 0 < M)
    {p : ℕ × ℕ} (hp : p ∈ productPairs N M) :
    0 < p.1*p.2 ∧ N*M < p.1*p.2 ∧ p.1*p.2 < 4*(N*M) := by
  obtain ⟨hn, hq⟩ := Finset.mem_product.mp hp
  obtain ⟨hnlo, hnhi⟩ := Finset.mem_Ioc.mp hn
  obtain ⟨hqlo, hqhi⟩ := Finset.mem_Ico.mp hq
  have hqpos : 0 < p.2 := hM.trans_le hqlo
  have hnpos : 0 < p.1 := by omega
  refine ⟨Nat.mul_pos hnpos hqpos, ?_, ?_⟩
  · exact (Nat.mul_lt_mul_of_pos_right hnlo hM).trans_le (Nat.mul_le_mul_left _ hqlo)
  · have hh := Nat.mul_lt_mul_of_pos_left hqhi hnpos
    have hi := Nat.mul_le_mul_right (2*M) hnhi
    nlinarith

theorem divisorMaximum_ge_one {T : ℝ} (hT : 0 ≤ T) : 1 ≤ divisorMaximum T := by
  have hmem : 1 ∈ Finset.Icc 1 ⌈32*(T+1)⌉₊ := by
    apply Finset.mem_Icc.mpr
    refine ⟨le_rfl, ?_⟩
    have hh := Nat.le_ceil (32*(T+1))
    have hi : (1 : ℝ) ≤ (⌈32*(T+1)⌉₊ : ℝ) := by linarith
    exact_mod_cast hi
  simpa only [divisorMaximum, Nat.divisors_one, Finset.card_singleton] using
    (Finset.le_sup (f := fun m : ℕ => m.divisors.card) hmem)

theorem original_product_divisors_le {T : ℝ} {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hscale : (N : ℝ)*M ≤ 8*(T+1)) {p : ℕ × ℕ} (hp : p ∈ productPairs N M) :
    (p.1*p.2).divisors.card ≤ divisorMaximum T := by
  obtain ⟨hp0, _, hphi⟩ := product_range hN hM hp
  unfold divisorMaximum
  apply Finset.le_sup (f := fun m : ℕ => m.divisors.card) (b := p.1*p.2)
  apply Finset.mem_Icc.mpr
  refine ⟨hp0, ?_⟩
  have hi : ((p.1*p.2 : ℕ) : ℝ) < 4*((N : ℝ)*M) := by exact_mod_cast hphi
  have hc := Nat.le_ceil (32*(T+1))
  have hh : ((p.1*p.2 : ℕ) : ℝ) ≤ (⌈32*(T+1)⌉₊ : ℝ) := by linarith
  exact_mod_cast hh

theorem product_cutoff_one (w : ComparisonCutoff) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {p : ℕ × ℕ} (hp : p ∈ productPairs N M) :
    w (((p.1*p.2 : ℕ) : ℝ)/((N : ℝ)*M)) = 1 := by
  have hh := product_range hN hM hp
  have hL : (0 : ℝ) < (N : ℝ)*M := by positivity
  have hlo : (N : ℝ)*M < ((p.1*p.2 : ℕ) : ℝ) := by exact_mod_cast hh.2.1
  have hhi : ((p.1*p.2 : ℕ) : ℝ) < 4*((N : ℝ)*M) := by exact_mod_cast hh.2.2
  apply w.one_on
  constructor
  · exact (le_div_iff₀ hL).2 (by simpa only [one_mul] using hlo.le)
  · exact (div_le_iff₀ hL).2 hhi.le

/-- Group only original products, bound their multiplicities, then extend using the cutoff. -/
theorem product_grouping_cutoff (w : ComparisonCutoff) {T : ℝ} {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (hscale : (N : ℝ)*M ≤ 8*(T+1))
    (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m) :
    (∑ n ∈ Finset.Ioc N (2*N), ∑ q ∈ Finset.Ico M (2*M), F (n*q)) ≤
      (divisorMaximum T : ℝ) *
        ∑ m ∈ Finset.range (⌈5*((N : ℝ)*M)⌉₊+1), w (m/((N : ℝ)*M))*F m := by
  let P := productPairs N M
  let S := P.image (fun p => p.1*p.2)
  let R := Finset.range (⌈5*((N : ℝ)*M)⌉₊+1)
  have hL : (0 : ℝ) < (N : ℝ)*M := by positivity
  have hsub : S ⊆ R := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hm
    have hh := (product_range hN hM hp).2.2
    have hr : ((p.1*p.2 : ℕ) : ℝ) < 5*((N : ℝ)*M) := by
      have hi : ((p.1*p.2 : ℕ) : ℝ) < 4*((N : ℝ)*M) := by exact_mod_cast hh
      linarith
    have hc := Nat.le_ceil (5*((N : ℝ)*M))
    have hb : p.1*p.2 ≤ ⌈5*((N : ℝ)*M)⌉₊ := by exact_mod_cast hr.le.trans hc
    exact Finset.mem_range.mpr (by omega)
  have hgroup : (∑ p ∈ P, F (p.1*p.2)) =
      ∑ m ∈ S, (productMultiplicity N M m : ℝ)*F m := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P) (t := S)
      (g := fun p : ℕ × ℕ => p.1*p.2)
      (fun p hp => Finset.mem_image.mpr ⟨p, hp, rfl⟩)
      (fun p : ℕ × ℕ => F (p.1*p.2))]
    apply Finset.sum_congr rfl
    intro m hm
    calc
      _ = ∑ _p ∈ P.filter (fun p => p.1*p.2=m), F m := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
      _ = _ := by simp [productMultiplicity, P]
  calc
    _ = ∑ p ∈ P, F (p.1*p.2) := (Finset.sum_product _ _ _).symm
    _ = ∑ m ∈ S, (productMultiplicity N M m : ℝ)*F m := hgroup
    _ ≤ ∑ m ∈ S, (divisorMaximum T : ℝ)*(w (m/((N : ℝ)*M))*F m) := by
      apply Finset.sum_le_sum
      intro m hm
      obtain ⟨p, hp, he⟩ := Finset.mem_image.mp hm
      subst m
      rw [product_cutoff_one w hN hM hp, one_mul]
      apply mul_le_mul_of_nonneg_right _ (hF _)
      exact_mod_cast (productMultiplicity_le_divisors (product_range hN hM hp).1.ne').trans
        (original_product_divisors_le hN hM hscale hp)
    _ ≤ ∑ m ∈ R, (divisorMaximum T : ℝ)*(w (m/((N : ℝ)*M))*F m) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun m _ _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (w.nonneg _) (hF m)))
    _ = _ := (Finset.mul_sum _ _ _).symm

end MathCollab.Density
