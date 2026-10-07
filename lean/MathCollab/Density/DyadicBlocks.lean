module
public import MathCollab.Density.FixedBandError
public import MathCollab.Density.CompletePairs
public import Mathlib.Data.Nat.Log

@[expose] public section

open Real Complex Set
open scoped BigOperators

noncomputable section
namespace MathCollab.Density

def reflectionNatBand (L H : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌈4*H/(Real.pi*L)⌉₊).filter (fun m => inReflectionBand L H (m : ℤ))

theorem mem_reflectionNatBand (L H : ℝ) (m : ℕ) :
    m ∈ reflectionNatBand L H ↔ inReflectionBand L H (m : ℤ) := by
  constructor
  · exact fun hm => (Finset.mem_filter.mp hm).2
  · intro hm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨by have := hm.1; omega, ?_⟩, hm⟩
    have hh := hm.2.2.trans (Nat.le_ceil (4*H/(Real.pi*L)))
    exact_mod_cast hh

theorem sum_reflectionBand_eq_nat {E : Type*} [AddCommMonoid E]
    (L H : ℝ) (f : ℤ → E) :
    (∑ m ∈ reflectionBand L H, f m) = ∑ m ∈ reflectionNatBand L H, f (m : ℤ) := by
  apply Finset.sum_bij (fun m _ => m.toNat)
  · intro m hm
    have hb := (mem_reflectionBand L H m).1 hm
    apply (mem_reflectionNatBand L H _).2
    simpa only [Int.toNat_of_nonneg hb.1.le] using hb
  · intro m hm n hn he
    have hm0 := ((mem_reflectionBand L H m).1 hm).1.le
    have hn0 := ((mem_reflectionBand L H n).1 hn).1.le
    have hh := congrArg (fun x : ℕ => (x : ℤ)) he
    simpa only [Int.toNat_of_nonneg hm0, Int.toNat_of_nonneg hn0] using hh
  · intro n hn
    refine ⟨(n : ℤ), (mem_reflectionBand L H _).2 ((mem_reflectionNatBand L H n).1 hn), ?_⟩
    simp
  · intro m hm
    have hm0 := ((mem_reflectionBand L H m).1 hm).1.le
    simp only [Int.toNat_of_nonneg hm0]

def dyadicExponents (L H : ℝ) : Finset ℕ := (reflectionNatBand L H).image Nat.log2

def reflectionBlocks (L H : ℝ) : Finset ℕ := (dyadicExponents L H).image (fun j => 2^j)

theorem log2_block_bounds {m : ℕ} (hm : 0 < m) : 2^m.log2 ≤ m ∧ m < 2*(2^m.log2) := by
  constructor
  · exact (Nat.le_log2 hm.ne').1 le_rfl
  · have hh := (Nat.log2_lt hm.ne').1 (Nat.lt_succ_self m.log2)
    simpa only [pow_succ, mul_comm] using hh

theorem mem_dyadicExponents (L H : ℝ) (j : ℕ) :
    j ∈ dyadicExponents L H ↔ ∃ m ∈ reflectionNatBand L H, m.log2 = j := by
  exact Finset.mem_image

theorem dyadicExponent_scale_bounds {L H : ℝ} (hL : 0 < L) (_hH : 0 < H)
    {j : ℕ} (hj : j ∈ dyadicExponents L H) :
    H/(40*Real.pi*L) ≤ (2 : ℝ)^j ∧ (2 : ℝ)^j ≤ 4*H/(Real.pi*L) := by
  obtain ⟨m, hm, he⟩ := (mem_dyadicExponents L H j).1 hj
  have hb := (mem_reflectionNatBand L H m).1 hm
  have hmpos : 0 < m := by have := hb.1; omega
  have hbounds := log2_block_bounds hmpos
  rw [he] at hbounds
  have hmlo : (2 : ℝ)^j ≤ m := by exact_mod_cast hbounds.1
  have hmhi : (m : ℝ) < 2*(2 : ℝ)^j := by exact_mod_cast hbounds.2
  have hlo : H/(20*Real.pi*L) ≤ (m : ℝ) := by exact_mod_cast hb.2.1
  have hhi : (m : ℝ) ≤ 4*H/(Real.pi*L) := by exact_mod_cast hb.2.2
  constructor
  · have hh := (div_le_iff₀ (by positivity : 0 < 20*Real.pi*L)).1 hlo
    apply (div_le_iff₀ (by positivity : 0 < 40*Real.pi*L)).2
    nlinarith [mul_lt_mul_of_pos_right hmhi (show 0 < 20*Real.pi*L by positivity)]
  · exact hmlo.trans hhi

theorem dyadicExponents_card_le {L H : ℝ} (hL : 0 < L) (hH : 0 < H) :
    (dyadicExponents L H).card ≤ 10 := by
  by_cases hn : (dyadicExponents L H).Nonempty
  · let j₀ := (dyadicExponents L H).min' hn
    have hj₀ : j₀ ∈ dyadicExponents L H := Finset.min'_mem _ hn
    have hs : dyadicExponents L H ⊆ Finset.Icc j₀ (j₀+9) := by
      intro j hj
      apply Finset.mem_Icc.mpr
      refine ⟨Finset.min'_le _ _ hj, ?_⟩
      by_contra hnot
      have hgap : j₀+10 ≤ j := by omega
      have hp : (2 : ℝ)^(j₀+10) ≤ (2 : ℝ)^j :=
        pow_le_pow_right₀ (by norm_num) hgap
      have hhj := (dyadicExponent_scale_bounds hL hH hj).2
      have hh₀ := (dyadicExponent_scale_bounds hL hH hj₀).1
      have he : 4*H/(Real.pi*L) = 160*(H/(40*Real.pi*L)) := by field_simp; ring
      rw [he] at hhj
      rw [pow_add] at hp
      norm_num at hp
      have hpos : 0 < (2 : ℝ)^j₀ := by positivity
      nlinarith
    exact (Finset.card_le_card hs).trans (by simp; omega)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.card_empty, Nat.zero_le]

theorem reflectionBlocks_card_le {L H : ℝ} (hL : 0 < L) (hH : 0 < H) :
    (reflectionBlocks L H).card ≤ 10 :=
  Finset.card_image_le.trans (dyadicExponents_card_le hL hH)

theorem reflectionBlock_scale_bounds {L H : ℝ} (hL : 0 < L) (hH : 0 < H)
    {M : ℕ} (hM : M ∈ reflectionBlocks L H) :
    0 < M ∧ H/(40*Real.pi*L) ≤ (M : ℝ) ∧ (M : ℝ) ≤ 4*H/(Real.pi*L) := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hM
  have hh := dyadicExponent_scale_bounds hL hH hj
  exact ⟨by positivity, by exact_mod_cast hh.1, by exact_mod_cast hh.2⟩

theorem log2_eq_iff_block {m j : ℕ} (hm : 0 < m) :
    m.log2 = j ↔ 2^j ≤ m ∧ m < 2*(2^j) := by
  constructor
  · intro he
    simpa only [he] using log2_block_bounds hm
  · intro hh
    have hlo := (Nat.le_log2 hm.ne').2 hh.1
    have hhi : m.log2 < j+1 := (Nat.log2_lt hm.ne').2 (by simpa [pow_succ, mul_comm] using hh.2)
    omega

theorem natBand_filter_log2 (L H : ℝ) (j : ℕ) :
    (reflectionNatBand L H).filter (fun m => m.log2 = j) =
      (Finset.Ico (2^j) (2*(2^j))).filter (fun m => m ∈ reflectionNatBand L H) := by
  ext m
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨hm, hj⟩
    have hmpos : 0 < m := by
      have hh := ((mem_reflectionNatBand L H m).1 hm).1
      omega
    exact ⟨(log2_eq_iff_block hmpos).1 hj, hm⟩
  · rintro ⟨hb, hm⟩
    have hmpos : 0 < m := (by positivity : 0 < 2^j).trans_le hb.1
    exact ⟨hm, (log2_eq_iff_block hmpos).2 hb⟩

theorem dirichletPhase_add (x a b : ℝ) :
    dirichletPhase x (a+b) = dirichletPhase x a * dirichletPhase x b := by
  unfold dirichletPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem dirichletPhase_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (v : ℝ) :
    dirichletPhase (x*y) v = dirichletPhase x v * dirichletPhase y v := by
  unfold dirichletPhase
  rw [Real.log_mul hx.ne' hy.ne', ← Complex.exp_add]
  congr 1
  push_cast
  ring

def blockCoefficient (L H r : ℝ) (q : ℕ) : ℂ :=
  if q ∈ reflectionNatBand L H then dirichletPhase ((q : ℝ)*L) r else 0

def blockPolynomial (L H : ℝ) (M : ℕ) (r v : ℝ) : ℂ :=
  ∑ q ∈ Finset.Ico M (2*M), blockCoefficient L H r q * dirichletPhase ((q : ℝ)/M) (-v)

theorem norm_blockCoefficient_le (L H r : ℝ) (q : ℕ) : ‖blockCoefficient L H r q‖ ≤ 1 := by
  unfold blockCoefficient
  split_ifs
  · simp [dirichletPhase, Complex.norm_exp]
  · simp

theorem fiber_phaseSum_eq {L : ℝ} (hL : 0 < L) (H v r : ℝ) (j : ℕ) :
    (∑ q ∈ (reflectionNatBand L H).filter (fun q => q.log2 = j),
      dirichletPhase ((q : ℝ)*L) (r-v)) =
      dirichletPhase (((2^j : ℕ) : ℝ)*L) (-v) * blockPolynomial L H (2^j) r v := by
  rw [natBand_filter_log2, Finset.sum_filter, blockPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqb : q ∈ reflectionNatBand L H
  · simp only [hqb, ↓reduceIte, blockCoefficient]
    have hM : (0 : ℝ) < (2^j : ℕ) := by positivity
    have hqpos : (0 : ℝ) < q := by
      have hle := (Finset.mem_Ico.mp hq).1
      have : 0 < q := (by positivity : 0 < 2^j).trans_le hle
      exact_mod_cast this
    have he : (q : ℝ)*L = ((q : ℝ)/(2^j : ℕ))*(((2^j : ℕ) : ℝ)*L) := by field_simp
    rw [sub_eq_add_neg, dirichletPhase_add]
    have hp : dirichletPhase ((q : ℝ)*L) (-v) =
        dirichletPhase ((q : ℝ)/(2^j : ℕ)) (-v) *
          dirichletPhase (((2^j : ℕ) : ℝ)*L) (-v) := by
      rw [he]
      exact dirichletPhase_mul (div_pos hqpos hM) (mul_pos hM hL) (-v)
    rw [hp]
    ring
  · simp only [hqb, ↓reduceIte, blockCoefficient, zero_mul, mul_zero]

theorem sum_reflectionBlocks {E : Type*} [AddCommMonoid E] (L H : ℝ) (f : ℕ → E) :
    (∑ M ∈ reflectionBlocks L H, f M) = ∑ j ∈ dyadicExponents L H, f (2^j) := by
  apply Finset.sum_image
  intro j _ k _ he
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) he

/-- The implemented blocks are exactly the dyadic intervals intersecting the fixed band. -/
theorem mem_reflectionBlocks_iff (L H : ℝ) (M : ℕ) :
    M ∈ reflectionBlocks L H ↔ ∃ j : ℕ, M = 2^j ∧
      ∃ m ∈ reflectionNatBand L H, M ≤ m ∧ m < 2*M := by
  constructor
  · intro hM
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hM
    obtain ⟨m, hm, he⟩ := (mem_dyadicExponents L H j).1 hj
    have hmpos : 0 < m := by
      have hh := ((mem_reflectionNatBand L H m).1 hm).1
      omega
    exact ⟨j, rfl, m, hm, (log2_eq_iff_block hmpos).1 he⟩
  · rintro ⟨j, rfl, m, hm, hb⟩
    have hmpos : 0 < m := (by positivity : 0 < 2^j).trans_le hb.1
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, rfl⟩
    exact (mem_dyadicExponents L H j).2 ⟨m, hm, (log2_eq_iff_block hmpos).2 hb⟩

end MathCollab.Density
