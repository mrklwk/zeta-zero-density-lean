module
public import MathCollab.Density.DetectorIdentity
public import MathCollab.Density.MollifierBound
public import MathCollab.Density.DetectorParameters

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

/-- The normalized critical-line integral in the proved detector identity. -/
def detectorIntegral (ρ : ℂ) (X Y : ℝ) : ℂ :=
  (((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ,
    detectorKernel ρ X Y (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I))

/-- The dependence on the shifted ordinate costs a fixed factor, uniformly in q. -/
theorem detector_shifted_rpow_le {T γ v q : ℝ} (hT : 1 ≤ T)
    (hγ : |γ| ≤ 2*T) (hq : 0 ≤ q) (hq' : q ≤ 1) :
    (1+|γ+v|)^q ≤ 3*T^q*(1+|v|) := by
  have hbase : 1+|γ+v| ≤ 3*T*(1+|v|) := by
    have hab := abs_add_le γ v
    nlinarith [abs_nonneg v, mul_nonneg (show 0 ≤ T-1 by linarith) (abs_nonneg v),
      mul_nonneg (show 0 ≤ T by linarith) (abs_nonneg v)]
  calc
    _ ≤ (3*T*(1+|v|))^q := Real.rpow_le_rpow (by positivity) hbase hq
    _ = 3^q*T^q*(1+|v|)^q := by rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ 3*T^q*(1+|v|) := by
      have h3 : (3 : ℝ)^q ≤ 3 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hq'
      have hv : (1+|v|)^q ≤ 1+|v| := by simpa using Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg v] : 1 ≤ 1+|v|) hq'
      gcongr

/-- Conditional estimate: its only missing analytic input is the displayed
actual-zeta pointwise bound. The constant A precedes every exponent and scale. -/
theorem uniform_detector_integral_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (q C T X Y : ℝ) (ρ : ℂ),
      0 ≤ q → q ≤ 1 → 0 ≤ C → 1 ≤ T → 0 ≤ X → 0 < Y →
      3/4 ≤ ρ.re → ρ.re ≤ 1 → |ρ.im| ≤ 2*T →
      (∀ t : ℝ, ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ C*(1+|t|)^q) →
      ‖detectorIntegral ρ X Y‖ ≤ A*C*Real.sqrt X*Y^(1/2-ρ.re)*T^q := by
  obtain ⟨G, hG, hmass⟩ := uniform_detector_gamma_mass
  refine ⟨6*G, by positivity, ?_⟩
  intro q C T X Y ρ hq hq' hC hT hX hY hβ hβ' hγ hW
  let a : ℝ := 1/2-ρ.re
  let g := fun t : ℝ => Complex.Gamma ((a : ℂ)+(t : ℂ)*I)
  let F := fun t : ℝ => detectorKernel ρ X Y ((a : ℂ)+(t : ℂ)*I)
  let B : ℝ := 6*C*Real.sqrt X*Y^a*T^q
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have he : ∀ t : ℝ, ρ+((a : ℂ)+(t : ℂ)*I) = (1/2 : ℂ)+((ρ.im+t : ℝ) : ℂ)*I := by
    intro t
    apply Complex.ext <;> simp [a]
  have hb : ∀ t : ℝ, ‖F t‖ ≤ B*((1+|t|)*‖g t‖) := by
    intro t
    have hm := norm_zetaMollifier_le_two_sqrt (s := ρ+((a : ℂ)+(t : ℂ)*I)) hX (by rw [he]; norm_num)
    have hz := (hW (ρ.im+t)).trans (mul_le_mul_of_nonneg_left
      (detector_shifted_rpow_le hT hγ hq hq') hC)
    rw [← he] at hz
    dsimp [F, detectorKernel]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
    have hre : (((a : ℂ)+(t : ℂ)*I)).re = a := by simp
    rw [hre]
    calc
      _ ≤ (Y^a*‖g t‖)*(2*Real.sqrt X)*(C*(3*T^q*(1+|t|))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hz (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [B]; ring
  have hint := integrable_detectorKernel_left (X := X) hY hβ hβ'
  have hw := (hmass ρ.re hβ hβ').2.1
  have hm := (hmass ρ.re hβ hβ').2.2
  have hnorm : ‖∫ t : ℝ, F t‖ ≤ B*G := by
    calc
      _ ≤ ∫ t : ℝ, ‖F t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, B*((1+|t|)*‖g t‖) := integral_mono hint.norm (hw.const_mul B) hb
      _ = B*(∫ t : ℝ, (1+|t|)*‖g t‖) := integral_const_mul _ _
      _ ≤ B*G := mul_le_mul_of_nonneg_left hm hB
  have hc : ‖((1/(2*Real.pi) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    apply (div_le_one (by positivity)).2
    linarith [Real.pi_gt_three]
  change ‖((1/(2*Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul]
  calc
    _ ≤ 1*(B*G) := mul_le_mul hc hnorm (norm_nonneg _) (by norm_num)
    _ = _ := by dsimp [B, a]; ring

/-- The pole term estimate requires no growth bound for zeta. -/
theorem norm_detectorResidue_le {ρ : ℂ} {X Y : ℝ}
    (hX : 0 ≤ X) (hY : 0 < Y) (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hγ : 1 ≤ |ρ.im|) :
    ‖detectorResidue ρ X Y‖ ≤
      24*Real.sqrt X*Y^(1-ρ.re)*(1+|ρ.im|)*Real.exp (-|ρ.im|) := by
  have hm := norm_zetaMollifier_le_two_sqrt (s := 1) hX (by norm_num)
  have hg := norm_Gamma_one_sub_zero_le hβ hβ' hγ
  dsimp [detectorResidue]
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    _ ≤ Y^(1-ρ.re)*(12*(1+|ρ.im|)*Real.exp (-|ρ.im|))*(2*Real.sqrt X) := by gcongr
    _ = _ := by ring

/-- An explicit uniform pole majorant for the original detector parameters. -/
theorem norm_firstDetector_residue_le {ρ : ℂ} {T : ℝ}
    (hT : 1 ≤ T) (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re ≤ 1)
    (hγ : T ≤ |ρ.im|) (hγ' : |ρ.im| ≤ 2*T) :
    ‖detectorResidue ρ (firstDetectorX T) T‖ ≤ 72*T^3*Real.exp (-T) := by
  have hTpos : 0 < T := by linarith
  have hX : 0 ≤ firstDetectorX T := by unfold firstDetectorX; positivity
  have hXle : firstDetectorX T ≤ 2*T := by
    dsimp [firstDetectorX]
    have hp := Real.rpow_le_rpow_of_exponent_le hT (by norm_num : (1/8 : ℝ) ≤ 1)
    simpa using mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2)
  have hm := (norm_zetaMollifier_le_cutoff (firstDetectorX T) (s := 1) (by norm_num)).trans
    ((Nat.floor_le hX).trans hXle)
  have hg := norm_Gamma_one_sub_zero_le hβ hβ' (hT.trans hγ)
  have hp : T^(1-ρ.re) ≤ T := by simpa using Real.rpow_le_rpow_of_exponent_le hT (by linarith : 1-ρ.re ≤ 1)
  have hexp : Real.exp (-|ρ.im|) ≤ Real.exp (-T) := Real.exp_le_exp.mpr (by linarith)
  dsimp [detectorResidue]
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hTpos]
  simp only [Complex.sub_re, Complex.one_re]
  calc
    _ ≤ T*(12*(3*T)*Real.exp (-T))*(2*T) := by
      apply mul_le_mul _ hm (norm_nonneg _) (by positivity)
      apply mul_le_mul hp _ (norm_nonneg _) (by positivity)
      exact hg.trans (by gcongr; linarith)
    _ = _ := by ring

/-- The pole term is uniformly small with no Weyl dependency. -/
theorem firstDetector_residue_eventually_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      3/4 ≤ ρ.re → ρ.re ≤ 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      ‖detectorResidue ρ (firstDetectorX T) T‖ < δ := by
  have ht := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).const_mul 72
  simp only [mul_zero] at ht
  have he : ∀ᶠ T : ℝ in atTop, 72*T^3*Real.exp (-T) < δ := by
    simpa only [mul_zero, mul_assoc] using ht.eventually (gt_mem_nhds hδ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), he] with T hT hsmall
  intro ρ hβ hβ' hγ hγ'
  exact (norm_firstDetector_residue_le hT hβ hβ' hγ hγ').trans_lt hsmall

/-- Conditional on one explicit pointwise zeta estimate, the original detector
is uniformly small. The threshold precedes every actual zero in the slab. -/
theorem firstDetector_eventually_small_of_zeta_bound {η C δ : ℝ}
    (hη : 0 ≤ η) (hη' : η < 1/48) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hW : ∀ t : ℝ, ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ C*(1+|t|)^(1/6+η)) :
    ∀ᶠ T : ℝ in atTop, ∀ ρ : ℂ,
      3/4 ≤ ρ.re → ρ.re < 1 → T ≤ |ρ.im| → |ρ.im| ≤ 2*T →
      riemannZeta ρ = 0 →
      ‖smoothedDetector ρ (firstDetectorX T) (1/T)‖ < δ := by
  obtain ⟨A, hA, hbound⟩ := uniform_detector_integral_bound
  have ht := (first_detector_majorant_tendsto_zero hη').const_mul (A*C)
  simp only [mul_zero] at ht
  have he : ∀ᶠ T : ℝ in atTop, A*C*(Real.sqrt 2*T^(-1/48+η)) < δ/2 := by
    simpa only [mul_zero] using ht.eventually (gt_mem_nhds (show 0 < δ/2 by positivity))
  filter_upwards [eventually_ge_atTop (1 : ℝ), he,
    firstDetector_residue_eventually_small (show 0 < δ/2 by positivity)] with T hT hsmall hpole
  intro ρ hβ hβ' hγ hγ' hzero
  have hX : 0 ≤ firstDetectorX T := by unfold firstDetectorX; positivity
  have hi := hbound (1/6+η) C T (firstDetectorX T) T ρ (by linarith)
    (by linarith) hC hT hX (by linarith) hβ hβ'.le hγ' hW
  have hs := mul_le_mul_of_nonneg_left (first_detector_error_scale (η₀ := η) hT hβ)
    (show 0 ≤ A*C by positivity)
  have hint : ‖detectorIntegral ρ (firstDetectorX T) T‖ < δ/2 := by
    apply (hi.trans _).trans_lt hsmall
    simpa only [firstDetectorY, mul_assoc] using hs
  rw [smoothedDetector_contour_identity hT hβ hβ' hzero]
  change ‖detectorResidue ρ (firstDetectorX T) T + detectorIntegral ρ (firstDetectorX T) T‖ < δ
  exact (norm_add_le _ _).trans_lt (by linarith [hpole ρ hβ hβ'.le hγ hγ'])

end MathCollab.Density
