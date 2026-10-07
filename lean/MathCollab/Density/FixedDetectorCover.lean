module
public import MathCollab.Density.DetectorBlockExpansion
public import MathCollab.Density.DetectorFamilyScales

@[expose] public section

open Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- This finite set depends on T alone, before any zero is selected. -/
def fixedDetectorIndices (T : ℝ) : Finset (ℕ × ℕ) :=
  (Finset.range (detectorDyadicCount T)).product (Finset.range (detectorTaylorCutoff T+1))

theorem fixedDetectorIndices_card_le {T : ℝ}
    (hlog : 0 ≤ Real.log T)
    (hD : (detectorDyadicCount T : ℝ) ≤ 5*Real.log T)
    (hJ : (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T) :
    ((fixedDetectorIndices T).card : ℝ) ≤ 60*(Real.log T)^2 := by
  have h := mul_le_mul hD hJ (by positivity) (by positivity)
  calc
    _ = (detectorDyadicCount T : ℝ)*((detectorTaylorCutoff T : ℝ)+1) := by simp [fixedDetectorIndices]
    _ ≤ (5*Real.log T)*(12*Real.log T) := h
    _ = _ := by ring

/-- Quantitative tail control at the actual family cutoff. -/
theorem norm_fixedDetector_tail_le {T : ℝ} {N : ℕ} {ρ : ℂ}
    (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    ‖∑' j : ℕ, (detectorTaylorWeight ρ.re (j+(detectorTaylorCutoff T+1)) : ℂ)*
      detectorTaylorPolynomial T N (j+(detectorTaylorCutoff T+1)) ρ.im‖ ≤ 3*T^(-1 : ℝ) := by
  have hTpos : 0 < T := by linarith
  have hp : (1/3 : ℝ)^(detectorTaylorCutoff T+1) ≤ T^(-5 : ℝ) := by
    have hh : (1/3 : ℝ)^(detectorTaylorCutoff T+1) ≤ (1/3 : ℝ)^(detectorTaylorCutoff T) := by
      rw [pow_succ]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1/3 by norm_num) (detectorTaylorCutoff T)]
    exact hh.trans (detectorTaylorCutoff_geometric_le hT)
  calc
    _ ≤ 3*(N : ℝ)^2*(1/3 : ℝ)^(detectorTaylorCutoff T+1) :=
      norm_detectorTaylor_tail_le hTpos hN hβ hβ' _ _
    _ ≤ 3*(T^2)^2*T^(-5 : ℝ) := by gcongr
    _ = 3*T^(-1 : ℝ) := by
      rw [show (T^2)^2 = T^4 by ring, ← Real.rpow_natCast T 4, mul_assoc, ← Real.rpow_add hTpos]
      norm_num

/-- The fixed family has the full block height, up to an absolute constant. -/
theorem exists_fixedDetector_component {T : ℝ} {N : ℕ} {ρ : ℂ}
    (hT : 1 ≤ T) (hN : 0 < N) (hN' : (N : ℝ) ≤ T^2)
    (hβ : 0 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hsmall : 3*T^(-1 : ℝ) ≤ 1/(4*(detectorDyadicCount T : ℝ)))
    (hblock : 1/(2*(detectorDyadicCount T : ℝ)) ≤ ‖detectorBlock ρ T N‖) :
    ∃ j ∈ Finset.range (detectorTaylorCutoff T+1),
      (N : ℝ)^ρ.re/(8*(detectorDyadicCount T : ℝ)) ≤ ‖detectorTaylorPolynomial T N j ρ.im‖ := by
  let D : ℝ := detectorDyadicCount T
  let J := detectorTaylorCutoff T
  let W := fun j : ℕ => (detectorTaylorWeight ρ.re j : ℂ)*detectorTaylorPolynomial T N j ρ.im
  have hD : 0 < D := by dsimp [D, detectorDyadicCount]; positivity
  have hp : 1 ≤ (N : ℝ)^ρ.re := Real.one_le_rpow (by exact_mod_cast hN) hβ
  have hfull := norm_detectorTaylor_tsum_ge hN hβ T
  have ht := (norm_fixedDetector_tail_le hT hN hN' hβ hβ').trans hsmall
  have hs := (hasSum_detectorTaylorPolynomial hN ρ T).summable.sum_add_tsum_nat_add (J+1)
  have hnorm : ‖∑' j, W j‖ ≤ ‖∑ j ∈ Finset.range (J+1), W j‖ + ‖∑' j, W (j+(J+1))‖ := by
    change (∑ j ∈ Finset.range (J+1), W j)+(∑' j, W (j+(J+1))) = (∑' j, W j) at hs
    rw [← hs]
    exact norm_add_le _ _
  have hpartial : (N : ℝ)^ρ.re/(4*D) ≤ ‖∑ j ∈ Finset.range (J+1), W j‖ := by
    have hb := mul_le_mul_of_nonneg_left hblock (Real.rpow_nonneg (Nat.cast_nonneg N) ρ.re)
    have ht' : ‖∑' j, W (j+(J+1))‖ ≤ (N : ℝ)^ρ.re/(4*D) := by
      exact ht.trans ((div_le_div_iff_of_pos_right (by positivity)).mpr hp)
    change (N : ℝ)^ρ.re*‖detectorBlock ρ T N‖ ≤ ‖∑' j, W j‖ at hfull
    change (N : ℝ)^ρ.re*(1/(2*D)) ≤ _ at hb
    have halg : (N : ℝ)^ρ.re*(1/(2*D)) = 2*((N : ℝ)^ρ.re/(4*D)) := by ring
    rw [halg] at hb
    linarith
  obtain ⟨j, hj, hlarge⟩ := exists_large_taylor_component hβ hβ' J (detectorTaylorPolynomial T N · ρ.im)
  refine ⟨j, hj, ?_⟩
  have hh := div_le_div_of_nonneg_right hpartial (by norm_num : (0 : ℝ) ≤ 2)
  change ‖∑ j ∈ Finset.range (J+1), W j‖/2 ≤ _ at hlarge
  exact (show (N : ℝ)^ρ.re/(8*D) = ((N : ℝ)^ρ.re/(4*D))/2 by ring).trans_le (hh.trans hlarge)

/-- Complete fixed-family coverage of every actual slab zero, conditional only
on the displayed actual-zeta pointwise bound. The threshold and family precede
both coordinates of the zero; no Type-I restriction or ordinate shift occurs. -/
theorem fixedDetector_cover_of_zeta_bound {η C : ℝ}
    (hη : 0 ≤ η) (hη' : η < 1/48) (hC : 0 ≤ C)
    (hW : ∀ t : ℝ, ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ C*(1+|t|)^(1/6+η)) :
    ∀ᶠ T : ℝ in atTop, ∀ (σ : ℝ) (ρ : ℂ),
      3/4 ≤ σ → σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ∃ p ∈ fixedDetectorIndices T,
        firstDetectorX T/2 < ((2^p.1 : ℕ) : ℝ) ∧
        ((2^p.1 : ℕ) : ℝ) < T*(Real.log T)^2 ∧
        ((2^p.1 : ℕ) : ℝ)^σ/(40*Real.log T) ≤ ‖detectorTaylorPolynomial T (2^p.1) p.2 ρ.im‖ := by
  filter_upwards [detector_family_scales_eventually,
    finiteDetector_eventually_large_of_zeta_bound hη hη' hC hW] with T hsc hfin
  obtain ⟨hT, hlog, hK, hD, hJ, hsmall⟩ := hsc
  intro σ ρ hσ hσβ hβ' hγ hγ' hzero
  have hβ : 3/4 ≤ ρ.re := hσ.trans hσβ
  have hlarge := hfin ρ hβ hβ' hγ hγ' hzero
  obtain ⟨r, hr, hblock⟩ := exists_detector_dyadic_block (by linarith : 1 ≤ T) (by norm_num : (0 : ℝ) < 1/2) hlarge
  let N : ℕ := 2^r
  have hN : 0 < N := by dsimp [N]; positivity
  have hDpos : (0 : ℝ) < detectorDyadicCount T := by unfold detectorDyadicCount; positivity
  have hb : 1/(2*(detectorDyadicCount T : ℝ)) ≤ ‖detectorBlock ρ T N‖ := by convert hblock using 1; ring
  have hbn : detectorBlock ρ T N ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hb)
  obtain ⟨hlo, hhi⟩ := detectorBlock_scale_bounds (by linarith : 0 < T) hbn
  have hN' : (N : ℝ) ≤ T^2 := hhi.le.trans ((Nat.le_ceil _).trans hK)
  obtain ⟨j, hj, hdetect⟩ := exists_fixedDetector_component (by linarith : 1 ≤ T) hN hN'
    (by linarith) hβ'.le hsmall hb
  refine ⟨(r,j), Finset.mem_product.mpr ⟨hr, hj⟩, hlo, hhi, ?_⟩
  have hp : (N : ℝ)^σ ≤ (N : ℝ)^ρ.re := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hσβ
  have hden : 8*(detectorDyadicCount T : ℝ) ≤ 40*Real.log T := by linarith
  change (N : ℝ)^σ/(40*Real.log T) ≤ _
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hden).trans
    ((div_le_div_of_nonneg_right hp (by positivity)).trans hdetect)

end MathCollab.Density
