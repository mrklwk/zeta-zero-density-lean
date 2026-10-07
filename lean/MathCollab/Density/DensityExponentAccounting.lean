module
public import MathCollab.Density.DetectorAdmissibility

@[expose] public section

open Real Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- Exact exponent accounting for normalized polynomial heights. -/
theorem normalizedHeight_quotient {T L σ η : ℝ} (hT : 0 < T) (hL : 0 < L)
    (m k : ℕ) :
    L^m/(L^σ*T^(-2*η))^k = L^((m : ℝ)-σ*k)*T^(2*η*k) := by
  rw [mul_pow, div_mul_eq_div_div, ← Real.rpow_mul_natCast hL.le,
    ← Real.rpow_natCast L m, ← Real.rpow_sub hL,
    ← Real.rpow_mul_natCast hT.le, div_eq_mul_inv, ← Real.rpow_neg hT.le]
  congr 1
  congr 1
  ring

/-- For q in [0,1/2], the ambient logarithmic enlargement costs at most one log. -/
theorem densityAmbient_small_rpow {T q : ℝ} (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T)
    (_hq : 0 ≤ q) (hq' : q ≤ 1/2) :
    (densityAmbient T)^q ≤ 32*T^q*Real.log T := by
  have hTpos : 0 < T := by linarith
  have hlogpos : 0 < Real.log T := by linarith
  have hc : (32 : ℝ)^q ≤ 32 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 32) (show q ≤ 1 by linarith)
  have hl : ((Real.log T)^2)^q ≤ Real.log T := by
    rw [← Real.rpow_natCast_mul hlogpos.le]
    have hh := Real.rpow_le_rpow_of_exponent_le hlog (show (2 : ℝ)*q ≤ 1 by linarith)
    simpa only [Real.rpow_one, Nat.cast_ofNat] using hh
  rw [densityAmbient, Real.mul_rpow (by positivity) (by positivity),
    Real.mul_rpow (by norm_num) hTpos.le]
  exact mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity)) hl (by positivity) (by positivity)

/-- The two large-values terms use opposite scale endpoints. The negative
exponent 3-4sigma is evaluated at sqrt(T), retaining the target density exponent. -/
theorem density_largeValue_term_le {T L σ η : ℝ}
    (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T) (hσ : 3/4 ≤ σ) (hσ' : σ ≤ 1)
    (hη : 0 ≤ η) (hlo : Real.sqrt T ≤ L) (hhi : L ≤ densityAmbient T) :
    L^2/(L^σ*T^(-2*η))^2+L^3*Real.sqrt (densityAmbient T)/(L^σ*T^(-2*η))^4 ≤
      64*Real.log T*T^(2*(1-σ)+8*η) := by
  have hTpos : 0 < T := by linarith
  have hLpos : 0 < L := (Real.sqrt_pos.mpr hTpos).trans_le hlo
  have hlow := Real.rpow_le_rpow_of_nonpos (Real.sqrt_pos.mpr hTpos) hlo
    (show 3-4*σ ≤ 0 by linarith)
  have hhigh := (Real.rpow_le_rpow hLpos.le hhi (show 0 ≤ 2-2*σ by linarith)).trans
    (densityAmbient_small_rpow hT hlog (show 0 ≤ 2-2*σ by linarith) (by linarith))
  have hsqrt : Real.sqrt (densityAmbient T) ≤ 32*T^(1/2 : ℝ)*Real.log T := by
    simpa only [Real.sqrt_eq_rpow] using densityAmbient_small_rpow hT hlog
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1/2)
  have he₁ : T^(2-2*σ)*T^(4*η) = T^(2*(1-σ)+4*η) := by
    rw [← Real.rpow_add hTpos]
    congr 1
    ring
  have he₂ : (Real.sqrt T)^(3-4*σ)*T^(1/2 : ℝ)*T^(8*η) = T^(2*(1-σ)+8*η) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hTpos.le, ← Real.rpow_add hTpos,
      ← Real.rpow_add hTpos]
    congr 1
    ring
  have hp : T^(2*(1-σ)+4*η) ≤ T^(2*(1-σ)+8*η) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hfirst : L^2/(L^σ*T^(-2*η))^2 ≤ 32*Real.log T*T^(2*(1-σ)+8*η) := by
    rw [normalizedHeight_quotient hTpos hLpos]
    norm_num only [Nat.cast_ofNat]
    have hh := mul_le_mul_of_nonneg_right hhigh (show 0 ≤ T^(4*η) by positivity)
    calc
      _ = L^(2-2*σ)*T^(4*η) := by congr 1 <;> congr 1 <;> ring
      _ ≤ (32*T^(2-2*σ)*Real.log T)*T^(4*η) := hh
      _ = 32*Real.log T*T^(2*(1-σ)+4*η) := by rw [← he₁]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  have hsecond : L^3*Real.sqrt (densityAmbient T)/(L^σ*T^(-2*η))^4 ≤
      32*Real.log T*T^(2*(1-σ)+8*η) := by
    rw [mul_div_right_comm, normalizedHeight_quotient hTpos hLpos]
    norm_num only [Nat.cast_ofNat]
    have hh := mul_le_mul hlow hsqrt (Real.sqrt_nonneg _) (by positivity)
    have hh' := mul_le_mul_of_nonneg_right hh (show 0 ≤ T^(8*η) by positivity)
    calc
      _ = (L^(3-4*σ)*Real.sqrt (densityAmbient T))*T^(8*η) := by
        rw [show 3-σ*4 = 3-4*σ by ring, show 2*η*4 = 8*η by ring]
        ring
      _ ≤ ((Real.sqrt T)^(3-4*σ)*(32*T^(1/2 : ℝ)*Real.log T))*T^(8*η) := hh'
      _ = 32*Real.log T*T^(2*(1-σ)+8*η) := by rw [← he₂]; ring
  linarith

/-- The remaining four logarithms cost exactly 2eta, independently of sigma. -/
theorem density_logarithms_eventually {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, (Real.log T)^4 ≤ T^(2*η) := by
  have hl := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) (show 0 < 2*η by positivity)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (1 : ℝ), hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with T hT hh
  exact ((div_lt_iff₀ (by positivity : 0 < T^(2*η))).mp hh).le.trans_eq (one_mul _)

/-- Full 12eta accounting: 8eta in the two terms, 2eta for H^eta,
and 2eta for the family, local-count and scale logarithms. -/
theorem density_family_sum_eventually {η σ : ℝ}
    (hη : 0 < η) (hσ : 3/4 ≤ σ) (hσ' : σ ≤ 1) :
    ∀ᶠ T : ℝ in atTop,
      Real.log (2*T)*(densityAmbient T)^η*
        (∑ p ∈ poweredDetectorIndices T,
          ((poweredDetectorScale T p : ℝ)^2/
              ((poweredDetectorScale T p : ℝ)^σ*T^(-2*η))^2+
            (poweredDetectorScale T p : ℝ)^3*Real.sqrt (densityAmbient T)/
              ((poweredDetectorScale T p : ℝ)^σ*T^(-2*η))^4)) ≤
        30720*T^(2*(1-σ)+12*η) := by
  filter_upwards [detector_family_scales_eventually, densityAmbient_eventually_le_sq,
    density_logarithms_eventually hη] with T hsc hH hlogpow
  obtain ⟨hT, hlog, _, hD, hJ, _⟩ := hsc
  have hTpos : 0 < T := by linarith
  have hcard := poweredDetectorIndices_card_le (by linarith : 0 ≤ Real.log T) hD hJ
  have hsum : (∑ p ∈ poweredDetectorIndices T,
      ((poweredDetectorScale T p : ℝ)^2/((poweredDetectorScale T p : ℝ)^σ*T^(-2*η))^2+
      (poweredDetectorScale T p : ℝ)^3*Real.sqrt (densityAmbient T)/
        ((poweredDetectorScale T p : ℝ)^σ*T^(-2*η))^4)) ≤
      15360*(Real.log T)^3*T^(2*(1-σ)+8*η) := by
    calc
      _ ≤ ∑ _p ∈ poweredDetectorIndices T, 64*Real.log T*T^(2*(1-σ)+8*η) := by
        apply Finset.sum_le_sum
        intro p hp
        have hs := poweredDetectorFamily_scales (by linarith) hlog hp
        exact density_largeValue_term_le (by linarith) hlog hσ hσ' hη.le hs.2.1 (by linarith [hs.2.2])
      _ = ((poweredDetectorIndices T).card : ℝ)*(64*Real.log T*T^(2*(1-σ)+8*η)) := by simp
      _ ≤ (240*(Real.log T)^2)*(64*Real.log T*T^(2*(1-σ)+8*η)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring
  have hHpow : (densityAmbient T)^η ≤ T^(2*η) := by
    have hh := Real.rpow_le_rpow (show 0 ≤ densityAmbient T by unfold densityAmbient; positivity) hH hη.le
    rw [← Real.rpow_natCast_mul hTpos.le] at hh
    simpa only [Nat.cast_ofNat] using hh
  have hlogs : Real.log (2*T) ≤ 2*Real.log T := by
    rw [Real.log_mul (by norm_num) hTpos.ne']
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hT
    linarith
  have hHnonneg : 0 ≤ densityAmbient T := by unfold densityAmbient; positivity
  have hmul := mul_le_mul (mul_le_mul hlogs hHpow (by positivity) (by positivity)) hsum
    (by positivity) (by positivity)
  calc
    _ ≤ (2*Real.log T*T^(2*η))*(15360*(Real.log T)^3*T^(2*(1-σ)+8*η)) := hmul
    _ = 30720*(Real.log T)^4*(T^(2*η)*T^(2*(1-σ)+8*η)) := by ring
    _ ≤ 30720*T^(2*η)*(T^(2*η)*T^(2*(1-σ)+8*η)) := by gcongr
    _ = _ := by
      rw [mul_assoc (30720 : ℝ), ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
      congr 1
      congr 1
      ring

end MathCollab.Density
