module
public import MathCollab.Density.DetectorPoweredHeight

@[expose] public section

open Real Complex Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The powered family is selected from T alone, with all irrelevant scales
filtered before any zero is considered. -/
def poweredDetectorIndices (T : ℝ) : Finset ((ℕ × ℕ) × ℕ) :=
  ((fixedDetectorIndices T).product (Finset.range 4)).filter (fun p =>
    T^(1/8 : ℝ) < ((2^p.1.1 : ℕ) : ℝ) ∧
    ((2^p.1.1 : ℕ) : ℝ) ≤ T*(Real.log T)^2 ∧
    p.2 < detectorPower T (2^p.1.1))

def poweredDetectorScale (T : ℝ) (p : (ℕ × ℕ) × ℕ) : ℕ :=
  2^p.2*(2^p.1.1)^(detectorPower T (2^p.1.1))

def poweredDetectorFamilyCoeff (η T : ℝ) (p : (ℕ × ℕ) × ℕ) : ℕ → ℂ :=
  normalizedPoweredCoefficient η T (2^p.1.1) p.1.2 (detectorPower T (2^p.1.1))

theorem poweredDetectorIndices_card_le {T : ℝ}
    (hlog : 0 ≤ Real.log T)
    (hD : (detectorDyadicCount T : ℝ) ≤ 5*Real.log T)
    (hJ : (detectorTaylorCutoff T+1 : ℝ) ≤ 12*Real.log T) :
    ((poweredDetectorIndices T).card : ℝ) ≤ 240*(Real.log T)^2 := by
  have hf := fixedDetectorIndices_card_le hlog hD hJ
  have hc : (poweredDetectorIndices T).card ≤ (fixedDetectorIndices T).card*4 := by
    exact (Finset.card_filter_le ..).trans_eq (by simp)
  have hr : ((poweredDetectorIndices T).card : ℝ) ≤ ((fixedDetectorIndices T).card : ℝ)*4 := by exact_mod_cast hc
  linarith

theorem poweredDetectorFamily_scales {T : ℝ} {p : (ℕ × ℕ) × ℕ}
    (hT : 1 ≤ T) (hlog : 1 ≤ Real.log T) (hp : p ∈ poweredDetectorIndices T) :
    0 < poweredDetectorScale T p ∧
      Real.sqrt T ≤ (poweredDetectorScale T p : ℝ) ∧
      (2*(poweredDetectorScale T p) : ℝ) ≤ densityAmbient T := by
  obtain ⟨_, hlo, hhi, hℓ⟩ := Finset.mem_filter.mp hp
  let N := 2^p.1.1
  have hN : 0 < N := by dsimp [N]; positivity
  have hsc := detectorPower_piece_scales hT hlog hlo hhi hℓ
  refine ⟨by unfold poweredDetectorScale; positivity, hsc.1, ?_⟩
  have hk := (detectorPower_spec (by linarith : 0 ≤ T) hlo).2.1
  have hs := detectorPower_support_scale hT hlog hlo hhi
  have hpw : (2 : ℝ)^(p.2+1) ≤ 2^(detectorPower T N) :=
    pow_le_pow_right₀ (by norm_num) (by dsimp [N]; omega)
  have hm := mul_le_mul_of_nonneg_right hpw (show 0 ≤ (N : ℝ)^(detectorPower T N) by positivity)
  dsimp [poweredDetectorScale]
  dsimp [N] at hm
  push_cast at hs hm ⊢
  rw [mul_pow] at hs
  rw [pow_succ] at hm
  nlinarith

/-- Complete normalized powered coverage. The family and all coefficients
are fixed before sigma or rho; the only analytic premise is the displayed Weyl bound. -/
theorem poweredDetectorFamily_cover_of_zeta_bound {η η₀ C : ℝ}
    (hη : 0 < η) (hη₀ : 0 ≤ η₀) (hη₀' : η₀ < 1/48) (hC : 0 ≤ C)
    (hW : ∀ t : ℝ, ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ C*(1+|t|)^(1/6+η₀)) :
    ∀ᶠ T : ℝ in atTop, ∀ (σ : ℝ) (ρ : ℂ),
      3/4 ≤ σ → σ ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ∃ p ∈ poweredDetectorIndices T,
        (poweredDetectorScale T p : ℝ)^σ*T^(-2*η) ≤
          ‖detectingPolynomial (poweredDetectorScale T p) (poweredDetectorFamilyCoeff η T p) ρ.im‖ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    fixedDetector_cover_of_zeta_bound hη₀ hη₀' hC hW,
    exists_normalizedPowered_height hη] with T hT hc hp
  intro σ ρ hσ hσβ hβ hγ hγ' hzero
  obtain ⟨q, hq, hlo, hhi, hh⟩ := hc σ ρ hσ hσβ hβ hγ hγ' hzero
  have hlo' : T^(1/8 : ℝ) < ((2^q.1 : ℕ) : ℝ) := by
    simpa [firstDetectorX] using hlo
  have hk := detectorPower_spec (by linarith : 0 ≤ T) hlo'
  obtain ⟨ℓ, hℓ, hlarge⟩ := hp σ ρ.im (2^q.1) q.2 (detectorPower T (2^q.1))
    (by positivity) (by linarith) (by linarith) hk.1 hk.2.1 hh
  refine ⟨(q,ℓ), ?_, hlarge⟩
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨hq, Finset.mem_range.mpr ?_⟩,
    hlo', hhi.le, Finset.mem_range.mp hℓ⟩
  have := Finset.mem_range.mp hℓ
  omega

/-- Uniform normalization on the whole Ioc interval, including its right endpoint. -/
theorem poweredDetectorFamily_coefficients {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, ∀ p ∈ poweredDetectorIndices T,
      ∀ n ∈ Finset.Ioc (poweredDetectorScale T p) (2*poweredDetectorScale T p),
        ‖poweredDetectorFamilyCoeff η T p n‖ ≤ 1 := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
    normalizedPoweredCoefficient_eventually hη] with T hT hlog hc
  intro p hp n hn
  have hsc := poweredDetectorFamily_scales hT hlog hp
  obtain ⟨_, hlo, _, _⟩ := Finset.mem_filter.mp hp
  apply hc _ _ _ _ (by positivity) (detectorPower_spec (by linarith) hlo).2.1
  have hn' : (n : ℝ) ≤ 2*(poweredDetectorScale T p) := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  exact hn'.trans hsc.2.2

end MathCollab.Density
