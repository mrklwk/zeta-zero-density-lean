module
public import MathCollab.Density.FixedDetectorCover

@[expose] public section

open Real Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

def detectorPower (T : ℝ) (N : ℕ) : ℕ :=
  if Real.sqrt T ≤ (N : ℝ) then 1 else
  if Real.sqrt T ≤ (N : ℝ)^2 then 2 else
  if Real.sqrt T ≤ (N : ℝ)^3 then 3 else 4

def densityAmbient (T : ℝ) : ℝ := 32*T*(Real.log T)^2

/-- Least successful power among 1,2,3,4, fixed before the zero varies. -/
theorem detectorPower_spec {T : ℝ} {N : ℕ} (hT : 0 ≤ T)
    (hN : T^(1/8 : ℝ) < N) :
    1 ≤ detectorPower T N ∧ detectorPower T N ≤ 4 ∧
      Real.sqrt T ≤ (N : ℝ)^(detectorPower T N) ∧
      (detectorPower T N = 1 ∨
        ((N : ℝ)^(detectorPower T N-1) < Real.sqrt T ∧ (N : ℝ) < Real.sqrt T)) := by
  have h4 : Real.sqrt T < (N : ℝ)^4 := by
    have h := pow_lt_pow_left₀ hN (Real.rpow_nonneg hT _) (by norm_num : (4 : ℕ) ≠ 0)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT] at h
    norm_num at h
    simpa [Real.sqrt_eq_rpow] using h
  by_cases h1 : Real.sqrt T ≤ (N : ℝ)
  · simp [detectorPower, h1]
  · by_cases h2 : Real.sqrt T ≤ (N : ℝ)^2
    · simp [detectorPower, h1, h2, lt_of_not_ge h1]
    · by_cases h3 : Real.sqrt T ≤ (N : ℝ)^3
      · simp [detectorPower, h1, h2, h3, lt_of_not_ge h1, lt_of_not_ge h2]
      · simp [detectorPower, h1, h2, h3, h4.le, lt_of_not_ge h1, lt_of_not_ge h3]

/-- The power does not make the underlying product scale exceed T log(T)^2. -/
theorem detectorPower_base_le {T : ℝ} {N : ℕ}
    (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T)
    (hN : T^(1/8 : ℝ) < N) (hN' : (N : ℝ) ≤ T*(Real.log T)^2) :
    (N : ℝ)^(detectorPower T N) ≤ T*(Real.log T)^2 := by
  obtain ⟨hk, _, _, hmin⟩ := detectorPower_spec (by linarith) hN
  rcases hmin with he | ⟨hprev, hsmall⟩
  · simpa [he] using hN'
  · have hpow : (N : ℝ)^(detectorPower T N) < T := by
      rw [show detectorPower T N = (detectorPower T N-1)+1 by omega, pow_succ]
      have hm := mul_lt_mul hprev hsmall.le (lt_trans (Real.rpow_pos_of_pos (by linarith) _) hN) (Real.sqrt_nonneg T)
      simpa [Real.mul_self_sqrt (by linarith : 0 ≤ T)] using hm
    have hsq : 1 ≤ (Real.log T)^2 := by nlinarith
    exact hpow.le.trans (by nlinarith)

/-- Every dyadic support piece of the actual power is in the packet's scale band. -/
theorem detectorPower_piece_scales {T : ℝ} {N ℓ : ℕ}
    (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T)
    (hN : T^(1/8 : ℝ) < N) (hN' : (N : ℝ) ≤ T*(Real.log T)^2)
    (hℓ : ℓ < detectorPower T N) :
    Real.sqrt T ≤ ((2^ℓ*N^(detectorPower T N) : ℕ) : ℝ) ∧
      ((2^ℓ*N^(detectorPower T N) : ℕ) : ℝ) ≤ densityAmbient T := by
  obtain ⟨_, hk, hlower, _⟩ := detectorPower_spec (by linarith) hN
  have hbase := detectorPower_base_le hT hlog hN hN'
  have htwo : (1 : ℝ) ≤ 2^ℓ := one_le_pow₀ (by norm_num)
  have htwo' : (2 : ℝ)^ℓ ≤ 8 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show ℓ ≤ 3 by omega)
    norm_num at h ⊢
    exact h
  push_cast
  constructor
  · nlinarith [Real.rpow_nonneg (by linarith : 0 ≤ T) (1/8), pow_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (detectorPower T N)]
  · unfold densityAmbient
    have h := mul_le_mul htwo' hbase (by positivity) (by norm_num)
    nlinarith [show 0 ≤ T*(Real.log T)^2 by positivity]

theorem detectorPower_support_scale {T : ℝ} {N : ℕ}
    (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T)
    (hN : T^(1/8 : ℝ) < N) (hN' : (N : ℝ) ≤ T*(Real.log T)^2) :
    ((2*N : ℕ)^(detectorPower T N) : ℝ) ≤ densityAmbient T := by
  have hk := (detectorPower_spec (by linarith : 0 ≤ T) hN).2.1
  have hbase := detectorPower_base_le hT hlog hN hN'
  have htwo : (2 : ℝ)^(detectorPower T N) ≤ 16 := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    norm_num at h ⊢
    exact h
  push_cast
  rw [mul_pow]
  unfold densityAmbient
  have h := mul_le_mul htwo hbase (by positivity) (by norm_num)
  nlinarith [show 0 ≤ T*(Real.log T)^2 by positivity]

end MathCollab.Density
