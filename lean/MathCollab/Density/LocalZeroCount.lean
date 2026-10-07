module
/-
The Jensen proof is adapted from Scott McColm's ExtractSeparated.lean at
2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, MIT. The original Type-I set is
replaced by the existing actual-zero set; only rectangle membership is used.
-/
public import MathCollab.Density.ZetaJensenInputs
public import MathCollab.Density.ZeroSeparation

@[expose] public section

open Complex Filter Set MeasureTheory
open scoped Topology BigOperators
open MathCollab.Density.ZetaGrowth

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

theorem zeta_unit_bin_sum_le_jensen (σ T : ℝ) (z : ℤ)
    (hσLower : 7 / 10 ≤ σ) (hT : 8 ≤ T) :
    ((∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter
        (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1),
        zetaMultiplicity ρ : ℕ) : ℝ) ≤
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
        Real.log ((7/4 : ℝ) / (3/2 : ℝ)) := by
  let S := (zetaZeroFinset σ T (2*T)).filter
    (fun ρ => (z : ℝ) ≤ ρ.im ∧ ρ.im < (z : ℝ) + 1)
  by_cases hSEmpty : S = ∅
  · change ((∑ ρ ∈ S, zetaMultiplicity ρ : ℕ) : ℝ) ≤ _
    rw [hSEmpty]
    simp only [Finset.sum_empty, Nat.cast_zero]
    have hLogDen : 0 < Real.log ((7/4 : ℝ) / (3/2 : ℝ)) := by
      apply Real.log_pos
      norm_num
    have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        1 ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring
    have hRatio : 1 ≤ (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
      norm_num at hM ⊢
      nlinarith
    exact div_nonneg (Real.log_nonneg hRatio) hLogDen.le
  · have hSNonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hSEmpty
    obtain ⟨ρ₀, hρ₀⟩ := hSNonempty
    have hρ₀Data := Finset.mem_filter.mp hρ₀
    have hρ₀Rect : (σ ≤ ρ₀.re ∧ ρ₀.re ≤ 1 ∧ T ≤ ρ₀.im ∧ ρ₀.im ≤ 2*T) ∧
        riemannZeta ρ₀ = 0 := by
      obtain ⟨hz, hs, hlo, hhi⟩ := mem_zetaZeroFinset.mp hρ₀Data.1
      exact ⟨⟨hs, hz.2.2.le, hlo, hhi⟩, hz.1⟩
    have hzRange : (z : ℝ) ∈ Set.Icc (T - 1) (2 * T) := by
      constructor
      · linarith [hρ₀Rect.1.2.2.1, hρ₀Data.2.2]
      · linarith [hρ₀Rect.1.2.2.2, hρ₀Data.2.1]
    let c : ℂ := 2 + I * (((z : ℝ) + 1/2 : ℝ) : ℂ)
    let U : Set ℂ := Metric.closedBall c (7/4 : ℝ)
    have hUCompact : IsCompact U := isCompact_closedBall c (7/4 : ℝ)
    have hUPre : IsPreconnected U := (convex_closedBall c (7/4 : ℝ)).isPreconnected
    have hcU : c ∈ U := by
      simp only [U, Metric.mem_closedBall, dist_self]
      norm_num
    have hUAnalytic : AnalyticOnNhd ℂ riemannZeta U := by
      apply analyticOn_riemannZeta.mono
      intro w hw
      have hwNorm : ‖w - c‖ ≤ 7/4 := by
        simpa [U, Metric.mem_closedBall, dist_eq_norm] using hw
      have hwImDiff : |w.im - ((z : ℝ) + 1/2)| ≤ 7/4 := by
        calc
          |w.im - ((z : ℝ) + 1/2)| = |(w - c).im| := by simp [c]
          _ ≤ ‖w - c‖ := abs_im_le_norm _
          _ ≤ 7/4 := hwNorm
      have hwIm : 1 < w.im := by
        have := (abs_le.mp hwImDiff).1
        linarith [hzRange.1]
      intro hwOne
      subst w
      norm_num at hwIm
    have hcLower : (0.6 : ℝ) ≤ ‖riemannZeta c‖ := by
      simpa [c] using euler_product_lower_bound_2 (z : ℝ)
    have hcNe : riemannZeta c ≠ 0 := by
      intro hcZero
      rw [hcZero, norm_zero] at hcLower
      norm_num at hcLower
    have hcOrder : analyticOrderAt riemannZeta c ≠ ⊤ := by
      rw [analyticOrderAt_eq_zero.mpr (Or.inr hcNe)]
      exact ENat.natCast_ne_top 0
    have hSU : ∀ ρ ∈ S, ρ ∈ Metric.closedBall c (3/2 : ℝ) := by
      intro ρ hρ
      have hρData := Finset.mem_filter.mp hρ
      have hρRect : (σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ T ≤ ρ.im ∧ ρ.im ≤ 2*T) ∧
          riemannZeta ρ = 0 := by
        obtain ⟨hz, hs, hlo, hhi⟩ := mem_zetaZeroFinset.mp hρData.1
        exact ⟨⟨hs, hz.2.2.le, hlo, hhi⟩, hz.1⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hreLower : -(13/10 : ℝ) ≤ (ρ - c).re := by
        norm_num [c]
        linarith [hσLower, hρRect.1.1]
      have hreUpper : (ρ - c).re ≤ 0 := by
        norm_num [c]
        linarith [hρRect.1.2.1]
      have himLower : -(1/2 : ℝ) ≤ (ρ - c).im := by
        norm_num [c]
        linarith [hρData.2.1]
      have himUpper : (ρ - c).im ≤ 1/2 := by
        norm_num [c]
        linarith [hρData.2.2]
      rw [mul_self_le_mul_self_iff (norm_nonneg _) (by norm_num)]
      rw [Complex.norm_mul_self_eq_normSq, normSq_apply]
      nlinarith [sq_nonneg ((ρ - c).re + 13/10), sq_nonneg ((ρ - c).im + 1/2),
        sq_nonneg ((ρ - c).im - 1/2)]
    let V : Set ℂ := Metric.closedBall c (3/2 : ℝ)
    have hVCompact : IsCompact V := isCompact_closedBall c (3/2 : ℝ)
    have hVPre : IsPreconnected V := (convex_closedBall c (3/2 : ℝ)).isPreconnected
    have hcV : c ∈ V := by
      simp only [V, Metric.mem_closedBall, dist_self]
      norm_num
    have hVAnalytic : AnalyticOnNhd ℂ riemannZeta V :=
      hUAnalytic.mono (Metric.closedBall_subset_closedBall (by norm_num : (3/2 : ℝ) ≤ 7/4))
    have hSV : ∀ ρ ∈ S, ρ ∈ V := by simpa [V] using hSU
    have hBridge := finset_analyticOrderNatAt_le_finsum_divisor hVAnalytic hVCompact
      hVPre hcV hcOrder S hSV
    have hM : 1 ≤ 100 * T ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]
      have hT2 : 1 ≤ T ^ (2 : ℕ) := by nlinarith
      calc
        1 ≤ 100 * T := by nlinarith
        _ ≤ 100 * T * T ^ (2 : ℕ) := by nlinarith
        _ = 100 * T ^ (3 : ℕ) := by ring
    have hUAnalyticAbs : AnalyticOnNhd ℂ riemannZeta
        (Metric.closedBall c |(7/4 : ℝ)|) := by
      simpa [U, abs_of_pos (by norm_num : (0 : ℝ) < 7/4)] using hUAnalytic
    have hJensen := hUAnalyticAbs.sum_divisor_le
      (r := (3/2 : ℝ)) (R := (7/4 : ℝ)) (M := 100 * T ^ (3 : ℝ))
      (by norm_num) (by norm_num) hM hcNe (by
        intro w hw
        exact zeta_jensen_sphere_bound T (z : ℝ) hT hzRange w (by
          simpa [c, abs_of_pos (by norm_num : (0 : ℝ) < 7/4)] using hw))
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3/2)] at hJensen
    change ((∑ ρ ∈ S, zetaMultiplicity ρ : ℕ) : ℝ) ≤ _
    refine hBridge.trans (le_trans (by simpa [c, V]
      using hJensen) ?_)
    have hLogDen : 0 < Real.log ((7/4 : ℝ) / (3/2 : ℝ)) := by
      apply Real.log_pos
      norm_num
    apply div_le_div_of_nonneg_right _ hLogDen.le
    have hMPos : 0 < 100 * T ^ (3 : ℕ) := by positivity
    have hcNormPos : 0 < ‖riemannZeta c‖ := norm_pos_iff.mpr hcNe
    have hRatioLe : (100 * T ^ (3 : ℕ)) / ‖riemannZeta c‖ ≤
        (100 * T ^ (3 : ℕ)) / (0.6 : ℝ) :=
      div_le_div_of_nonneg_left hMPos.le (by norm_num) hcLower
    exact Real.log_le_log
      (div_pos hMPos (by simpa [c] using hcNormPos)) (by simpa [c] using hRatioLe)


/-- A single logarithmic multiplicity constant for every actual zero bin.
Both the large-height Jensen estimate and the bounded-height range are proved. -/
theorem zeta_local_multiplicity_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 3/4 ≤ σ → 2 ≤ T → ∀ k : ℤ,
      (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
        (zetaMultiplicity ρ : ℝ)) ≤ C*Real.log (2*T) := by
  classical
  let D : ℝ := Real.log ((7/4 : ℝ)/(3/2 : ℝ))
  let K : ℝ := 100/D
  let T₀ : ℝ := max (Real.exp 2) 8
  have hD : 0 < D := by dsimp [D]; apply Real.log_pos; norm_num
  have hK : 0 < K := div_pos (by norm_num) hD
  have hT₀ : 8 ≤ T₀ := le_max_right _ _
  have hlarge : ∀ σ T : ℝ, 3/4 ≤ σ → T₀ ≤ T → ∀ k : ℤ,
      (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
        (zetaMultiplicity ρ : ℝ)) ≤ K*Real.log (2*T) := by
    intro σ T hσ hT k
    have hT8 : 8 ≤ T := hT₀.trans hT
    have hTexp : Real.exp 2 ≤ T := (le_max_left _ _).trans hT
    have hTpos : 0 < T := by linarith
    have hlog : 2 ≤ Real.log T := by
      simpa using Real.log_le_log (Real.exp_pos 2) hTexp
    have hraw := zeta_unit_bin_sum_le_jensen σ T k (by linarith) hT8
    have hnum : Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ)) ≤ 100*Real.log T := by
      have hconst := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 500/3 by norm_num)
      calc
        Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ)) =
            Real.log ((500/3 : ℝ)*T^(3 : ℝ)) := by congr 1; ring
        _ = Real.log (500/3 : ℝ)+3*Real.log T := by
          rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hTpos 3).ne',
            Real.log_rpow hTpos]
        _ ≤ _ := by nlinarith
    have hcast :
        (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
          (zetaMultiplicity ρ : ℝ)) ≤
          Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ))/D := by
      simpa only [D, Nat.cast_sum, ordinateBin_eq_iff] using hraw
    calc
      _ ≤ Real.log ((100*T^(3 : ℝ))/(0.6 : ℝ))/D := hcast
      _ ≤ (100*Real.log T)/D := div_le_div_of_nonneg_right hnum hD.le
      _ = K*Real.log T := by dsimp [K]; ring
      _ ≤ K*Real.log (2*T) := mul_le_mul_of_nonneg_left
        (Real.log_le_log hTpos (by linarith)) hK.le
  let Q : ℝ := zetaDensityCount (3/4) (2*T₀)
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨K+Q/Real.log 4+1, by positivity, ?_⟩
  intro σ T hσ hT k
  have hTpos : 0 < T := by linarith
  have hloglow : Real.log 4 ≤ Real.log (2*T) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlognonneg : 0 ≤ Real.log (2*T) := hlog4.le.trans hloglow
  by_cases hlargeT : T₀ ≤ T
  · exact (hlarge σ T hσ hlargeT k).trans
      (mul_le_mul_of_nonneg_right (by
        have hq := div_nonneg hQ hlog4.le
        linarith) hlognonneg)
  · have hTupper : T ≤ T₀ := (not_le.mp hlargeT).le
    have hcount : zetaSlabCount σ T (2*T) ≤ zetaDensityCount (3/4) (2*T₀) :=
      zetaSlabCount_mono hσ (by linarith) (by linarith)
    have hfilter :
        (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
          zetaMultiplicity ρ) ≤ zetaSlabCount σ T (2*T) :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    have hsum :
        (∑ ρ ∈ (zetaZeroFinset σ T (2*T)).filter (fun ρ => ordinateBin ρ = k),
          (zetaMultiplicity ρ : ℝ)) ≤ Q := by
      dsimp [Q]
      exact_mod_cast hfilter.trans hcount
    calc
      _ ≤ Q := hsum
      _ = (Q/Real.log 4)*Real.log 4 := (div_mul_cancel₀ Q hlog4.ne').symm
      _ ≤ (Q/Real.log 4)*Real.log (2*T) :=
        mul_le_mul_of_nonneg_left hloglow (div_nonneg hQ hlog4.le)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hlognonneg

/-- Unconditional logarithmic restoration of all analytic multiplicities. -/
theorem zeta_separated_representatives :
    ∃ C : ℝ, 0 < C ∧ ∀ σ T : ℝ, 3/4 ≤ σ → 2 ≤ T →
      ∃ R : Finset ℂ, R ⊆ zetaZeroFinset σ T (2*T) ∧
        (R.image Complex.im).card = R.card ∧ oneSeparated (R.image Complex.im) ∧
        (zetaSlabCount σ T (2*T) : ℝ) ≤ C*Real.log (2*T)*(R.card : ℝ) := by
  obtain ⟨C, hC, hlocal⟩ := zeta_local_multiplicity_bound
  refine ⟨2*C, by positivity, ?_⟩
  intro σ T hσ hT
  have hB : 0 ≤ C*Real.log (2*T) := mul_nonneg hC.le
    (Real.log_nonneg (by linarith))
  obtain ⟨R, hR, hcard, hsep, hcount⟩ :=
    zetaSlab_separated_representatives σ T (2*T) hB (hlocal σ T hσ hT)
  refine ⟨R, hR, hcard, hsep, ?_⟩
  calc
    _ ≤ 2*(C*Real.log (2*T))*(R.card : ℝ) := hcount
    _ = _ := by ring

end MathCollab.Density
