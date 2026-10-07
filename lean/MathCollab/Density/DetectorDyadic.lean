module
public import MathCollab.Density.DetectorTaylorFamily

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

def detectorBlock (ρ : ℂ) (T : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), firstDetectorCoefficient T n*(n : ℂ)^(-ρ)

/-- The full finite list is fixed at T, before a zero is considered. -/
def detectorDyadicCount (T : ℝ) : ℕ := Nat.log 2 (firstDetectorCutoff T)+1

theorem sum_dyadic_Ioc (f : ℕ → ℂ) (L : ℕ) :
    (∑ r ∈ Finset.range L, ∑ n ∈ Finset.Ioc (2^r) (2*2^r), f n) =
      ∑ n ∈ Finset.Ioc 1 (2^L), f n := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    have he : 2^(L+1) = 2*2^L := by ring
    rw [he]
    exact Finset.sum_Ioc_consecutive f (by exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))) (by omega)

theorem finiteDetector_eq_dyadic_sum {T : ℝ} (hT : 1 ≤ T) (ρ : ℂ) :
    finiteDetector ρ T =
      ∑ r ∈ Finset.range (detectorDyadicCount T), detectorBlock ρ T (2^r) := by
  let K := firstDetectorCutoff T
  let L := detectorDyadicCount T
  let f := fun n : ℕ => firstDetectorCoefficient T n*(n : ℂ)^(-ρ)
  have hK : K < 2^L := Nat.lt_pow_succ_log_self (by norm_num) K
  have hX : 1 ≤ ⌊firstDetectorX T⌋₊ := Nat.le_floor (by simpa using firstDetectorX_one_le hT)
  have hs : ∑ n ∈ Finset.range K, f n = ∑ n ∈ Finset.range (2^L+1), f n := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro n hn hn'
    have hz : ¬ n < firstDetectorCutoff T := by simpa [K] using hn'
    simp [f, firstDetectorCoefficient, hz]
  have hi : ∑ n ∈ Finset.Ioc 1 (2^L), f n = ∑ n ∈ Finset.range (2^L+1), f n := by
    apply Finset.sum_subset
    · intro n hn
      exact Finset.mem_range.mpr (by have := (Finset.mem_Ioc.mp hn).2; omega)
    · intro n hn hn'
      have hnlow : n ≤ 1 := by
        have hnr := Finset.mem_range.mp hn
        have hni : ¬ (1 < n ∧ n ≤ 2^L) := by simpa using hn'
        omega
      have hz : ¬ ⌊firstDetectorX T⌋₊ < n := by omega
      simp [f, firstDetectorCoefficient, hz]
  change (∑ n ∈ Finset.range K, f n) = _
  rw [hs, ← hi, ← sum_dyadic_Ioc f L]
  rfl

/-- Quantitative extraction from the fixed dyadic list, without moving t. -/
theorem exists_detector_dyadic_block {T A : ℝ} {ρ : ℂ}
    (hT : 1 ≤ T) (hA : 0 < A) (hlarge : A ≤ ‖finiteDetector ρ T‖) :
    ∃ r ∈ Finset.range (detectorDyadicCount T),
      A/(detectorDyadicCount T : ℝ) ≤ ‖detectorBlock ρ T (2^r)‖ := by
  have hL : 0 < detectorDyadicCount T := by unfold detectorDyadicCount; omega
  have hLreal : (0 : ℝ) < detectorDyadicCount T := by exact_mod_cast hL
  by_contra h
  push Not at h
  have he : (∑ r ∈ Finset.range (detectorDyadicCount T), ‖detectorBlock ρ T (2^r)‖) < A := by
    calc
      _ < ∑ _r ∈ Finset.range (detectorDyadicCount T), A/(detectorDyadicCount T : ℝ) :=
        Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hL⟩ h
      _ = A := by simp; field_simp
  rw [finiteDetector_eq_dyadic_sum hT ρ] at hlarge
  have hb := norm_sum_le (Finset.range (detectorDyadicCount T)) (fun r => detectorBlock ρ T (2^r))
  linarith

/-- A nonzero block meets the true retained support, giving the packet's
strict lower block scale and its original logarithmic upper scale. -/
theorem detectorBlock_scale_bounds {T : ℝ} {N : ℕ} {ρ : ℂ}
    (hT : 0 < T) (hblock : detectorBlock ρ T N ≠ 0) :
    firstDetectorX T/2 < (N : ℝ) ∧ (N : ℝ) < T*(Real.log T)^2 := by
  obtain ⟨n, hn, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hblock
  have hc : firstDetectorCoefficient T n ≠ 0 := by
    intro he
    exact hterm (by rw [he, zero_mul])
  have hs := firstDetectorCoefficient_real_support hT hc
  have hlo : (N : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
  have hhi : (n : ℝ) ≤ 2*N := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  constructor <;> linarith

end MathCollab.Density
