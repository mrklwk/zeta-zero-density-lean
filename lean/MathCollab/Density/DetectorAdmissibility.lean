module
public import MathCollab.Density.PoweredDetectorFamily

@[expose] public section

open Real Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The ambient enlargement leaves room below the square-root lower scale. -/
theorem densityAmbient_eventually_cubeRoot_le :
    ∀ᶠ T : ℝ in atTop, (densityAmbient T)^(1/3 : ℝ) ≤ Real.sqrt T := by
  have hl := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (show (0 : ℝ) < 1/2 by norm_num)).tendsto_div_nhds_zero
  norm_num at hl
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    hl.eventually (gt_mem_nhds (show (0 : ℝ) < 1/32 by norm_num))] with T hT hh
  have hTpos : 0 < T := by linarith
  have hb := (div_lt_iff₀ (Real.rpow_pos_of_pos hTpos (1/2))).mp hh
  have he : T*T^(1/2 : ℝ) = T^(3/2 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one T]
    rw [← Real.rpow_add hTpos]
    norm_num
  have hH : densityAmbient T ≤ T^(3/2 : ℝ) := by
    unfold densityAmbient
    rw [← he]
    nlinarith
  calc
    _ ≤ (T^(3/2 : ℝ))^(1/3 : ℝ) :=
      Real.rpow_le_rpow (by unfold densityAmbient; positivity) hH (by norm_num)
    _ = Real.sqrt T := by rw [← Real.rpow_mul hTpos.le]; norm_num [Real.sqrt_eq_rpow]

theorem detectorHeight_ge_scale {T L σ η : ℝ}
    (hT : 0 < T) (hL : Real.sqrt T ≤ L) (hη : 0 ≤ η) :
    L^(σ-4*η) ≤ L^σ*T^(-2*η) := by
  have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hLp : 0 < L := hs.trans_le hL
  have hp := Real.rpow_le_rpow_of_nonpos hs hL (show -4*η ≤ 0 by linarith)
  have he : (Real.sqrt T)^(-4*η) = T^(-2*η) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le]
    congr 1
    ring
  rw [he] at hp
  rw [sub_eq_add_neg, Real.rpow_add hLp]
  simpa only [neg_mul] using mul_le_mul_of_nonneg_left hp (show 0 ≤ L^σ by positivity)

/-- All large-values admissibility conditions hold for every member of the
preselected finite family, with the original eta margin. -/
theorem poweredDetectorFamily_admissible {η κ σ : ℝ}
    (hη : 0 < η) (hmargin : 3/4+κ ≤ σ-4*η) :
    ∀ᶠ T : ℝ in atTop, 2 ≤ densityAmbient T ∧ 2*T ≤ T+densityAmbient T ∧
      ((poweredDetectorIndices T).card : ℝ) ≤ 240*(Real.log T)^2 ∧
      ∀ p ∈ poweredDetectorIndices T,
        0 < poweredDetectorScale T p ∧
        0 < (poweredDetectorScale T p : ℝ)^σ*T^(-2*η) ∧
        (densityAmbient T)^(1/3 : ℝ) ≤ (poweredDetectorScale T p : ℝ) ∧
        (poweredDetectorScale T p : ℝ) ≤ densityAmbient T ∧
        (poweredDetectorScale T p : ℝ)^(3/4+κ) ≤
          (poweredDetectorScale T p : ℝ)^σ*T^(-2*η) ∧
        ∀ n ∈ Finset.Ioc (poweredDetectorScale T p) (2*poweredDetectorScale T p),
          ‖poweredDetectorFamilyCoeff η T p n‖ ≤ 1 := by
  filter_upwards [detector_family_scales_eventually,
    densityAmbient_eventually_cubeRoot_le, poweredDetectorFamily_coefficients hη]
    with T hsc hroot hcoeff
  obtain ⟨hT, hlog, _, hD, hJ, _⟩ := hsc
  have hTpos : 0 < T := by linarith
  have hH : T ≤ densityAmbient T := by
    unfold densityAmbient
    nlinarith [sq_nonneg (Real.log T-1)]
  refine ⟨hT.trans hH, by linarith, poweredDetectorIndices_card_le (by linarith) hD hJ, ?_⟩
  intro p hp
  obtain ⟨hN, hlo, hhi⟩ := poweredDetectorFamily_scales (by linarith) hlog hp
  have hNreal : (0 : ℝ) < poweredDetectorScale T p := by exact_mod_cast hN
  refine ⟨hN, by positivity, hroot.trans hlo, by linarith, ?_, hcoeff p hp⟩
  calc
    _ ≤ (poweredDetectorScale T p : ℝ)^(σ-4*η) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hmargin
    _ ≤ _ := detectorHeight_ge_scale hTpos hlo hη.le

end MathCollab.Density
