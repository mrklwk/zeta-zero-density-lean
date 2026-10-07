module
public import WeylPort.AFE.UniformError
public import WeylPort.ShortSum

@[expose] public section

open Complex Finset Filter
open DhimanKadiriQuesadaHerrera2026
open scoped Topology

namespace WeylPort

/-- The AFE's literal sharp sum is the verified critical Dirichlet polynomial. -/
theorem norm_sharpZetaSum_critical (t x : ℝ) :
    ‖sharpZetaSum (criticalPoint t) x‖ =
      ‖∑ n ∈ Ico 1 (⌊x⌋₊+1), criticalTerm t n‖ := by
  simp only [sharpZetaSum,zetaTerm,criticalPoint,criticalTerm,Ico_add_one_right_eq_Icc]

/-- The dual sharp sum has the same norm, including the floor cutoff. -/
theorem norm_sharpZetaSum_dual (t y : ℝ) :
    ‖sharpZetaSum (1-criticalPoint t) y‖ =
      ‖∑ n ∈ Ico 1 (⌊y⌋₊+1), criticalTerm t n‖ := by
  simpa only [sharpZetaSum,zetaTerm,neg_sub,Ico_add_one_right_eq_Icc] using
    norm_dual_critical_sum t ⌊y⌋₊

/-- The actual zeta bound follows from the proved AFE with no analytic hypotheses.
The epsilon threshold precedes the height; both cutoff choices are internal. -/
theorem eventually_norm_riemannZeta_critical_lt_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ‖riemannZeta (criticalPoint t)‖ < t^(1/6+ε:ℝ) := by
  have ha : 0 < (1/6+ε:ℝ) := by linarith
  have hc := (tendsto_rpow_atTop ha).eventually
    (eventually_ge_atTop (4*criticalAFEConstant))
  filter_upwards [eventually_actual_zeta_short_afe,
    eventually_mul_norm_critical_sum_le_rpow 4 (by norm_num) hε,
    hc, eventually_ge_atTop (1:ℝ)] with t hafe hs hC ht
  obtain ⟨A,M,hA,hM,hR,hfloor⟩ := hafe
  let x : ℝ := (A:ℝ)+1/2
  let y : ℝ := t/(2*Real.pi*x)
  have hfx : ⌊x⌋₊ = A := (Nat.floor_eq_iff (by dsimp [x]; positivity)).mpr
    (by dsimp [x]; constructor <;> linarith)
  have hfy : ⌊y⌋₊ = M := hfloor
  have hsA := hs A hA
  have hsM := hs M hM
  have hid : riemannZeta (criticalPoint t) =
      afeRemainder (criticalPoint t) x y + sharpZetaSum (criticalPoint t) x +
        chi (criticalPoint t)*sharpZetaSum (1-criticalPoint t) y := by
    unfold afeRemainder
    ring
  have hb := (norm_add_le
    (afeRemainder (criticalPoint t) x y + sharpZetaSum (criticalPoint t) x)
    (chi (criticalPoint t)*sharpZetaSum (1-criticalPoint t) y)).trans
    (add_le_add (norm_add_le _ _) le_rfl)
  rw [← hid,norm_mul,norm_chi_criticalPoint,one_mul,
    norm_sharpZetaSum_critical,norm_sharpZetaSum_dual,hfx,hfy] at hb
  have hp : 0 < t^(1/6+ε:ℝ) := Real.rpow_pos_of_pos (by linarith) _
  change ‖afeRemainder (criticalPoint t) x y‖ ≤ criticalAFEConstant at hR
  nlinarith

/-- An explicit quantifier-order interface for sufficiently large positive heights. -/
theorem exists_riemannZeta_critical_lt_sixth_power {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ t : ℝ, T₀ ≤ t →
      ‖riemannZeta (criticalPoint t)‖ < t^(1/6+ε:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp (eventually_norm_riemannZeta_critical_lt_rpow hε)
  exact ⟨max 1 T,le_max_left _ _,fun t ht => hT t ((le_max_right _ _).trans ht)⟩

/-- Reflection gives equality of actual zeta norms at opposite heights. -/
theorem norm_riemannZeta_critical_neg (t : ℝ) :
    ‖riemannZeta (criticalPoint (-t))‖ = ‖riemannZeta (criticalPoint t)‖ := by
  rw [riemannZeta_critical_functional_equation (-t),norm_mul,norm_criticalGammaRatio,
    one_mul,one_sub_criticalPoint,← criticalPoint_neg,neg_neg]

/-- The critical line stays away from the sole pole. -/
theorem continuous_riemannZeta_critical :
    Continuous (fun t : ℝ => riemannZeta (criticalPoint t)) := by
  have hc : Continuous criticalPoint := by unfold criticalPoint; fun_prop
  apply continuous_iff_continuousAt.mpr
  intro t
  have hne : criticalPoint t ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    norm_num [criticalPoint] at this
  exact (differentiableAt_riemannZeta hne).continuousAt.comp hc.continuousAt

/-- Classical Weyl growth for actual zeta, including compact small heights and both signs. -/
theorem exists_riemannZeta_critical_weyl_all_heights {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖riemannZeta (criticalPoint t)‖ ≤ C*(max 1 |t|)^(1/6+ε:ℝ) := by
  obtain ⟨T,hT,hlarge⟩ := exists_riemannZeta_critical_lt_sixth_power hε
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) T)).exists_bound_of_continuousOn
    continuous_riemannZeta_critical.continuousOn
  let C := max 1 B
  have hC : 1 ≤ C := le_max_left _ _
  have ha : 0 ≤ (1/6+ε:ℝ) := by linarith
  refine ⟨C,by linarith,?_⟩
  intro t
  have he : ‖riemannZeta (criticalPoint t)‖ = ‖riemannZeta (criticalPoint |t|)‖ := by
    by_cases ht : 0 ≤ t
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg (lt_of_not_ge ht),norm_riemannZeta_critical_neg]
  rw [he]
  have hp : 1 ≤ (max 1 |t|)^(1/6+ε:ℝ) := Real.one_le_rpow (le_max_left _ _) ha
  by_cases ht : T ≤ |t|
  · have hb := (hlarge |t| ht).le
    have hpow : |t|^(1/6+ε:ℝ) ≤ (max 1 |t|)^(1/6+ε:ℝ) :=
      Real.rpow_le_rpow (abs_nonneg t) (le_max_right _ _) ha
    exact (hb.trans hpow).trans (by nlinarith)
  · have hb := hB |t| ⟨abs_nonneg t,le_of_not_ge ht⟩
    have hBC : B ≤ C := le_max_right _ _
    exact hb.trans (by nlinarith)

/-- Standard positive-height Weyl bound: the constant depends only on epsilon. -/
theorem exists_riemannZeta_critical_weyl {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 1 ≤ t →
      ‖riemannZeta ((1/2:ℂ)+(t:ℂ)*I)‖ ≤ C*t^(1/6+ε:ℝ) := by
  obtain ⟨C,hC,h⟩ := exists_riemannZeta_critical_weyl_all_heights hε
  refine ⟨C,hC,?_⟩
  intro t ht
  simpa only [criticalPoint,abs_of_nonneg (by linarith : 0 ≤ t),max_eq_right ht] using h t

/-- The dyadic-height contract of the newer source pointwise theorem, for actual zeta. -/
theorem exists_riemannZeta_critical_dyadic_weyl {ε : ℝ} (hε : 0 < ε) :
    ∃ H₀ : ℝ, 40000 ≤ H₀ ∧ ∀ H t : ℝ, H₀ ≤ H → H ≤ t → t ≤ 2*H →
      ‖riemannZeta (criticalPoint t)‖ < H^(1/6+ε:ℝ) := by
  have hhalf : 0 < ε/2 := by linarith
  obtain ⟨T,hT,hlarge⟩ := exists_riemannZeta_critical_lt_sixth_power hhalf
  have he := (tendsto_rpow_atTop hhalf).eventually
    (eventually_ge_atTop ((2:ℝ)^(1/6+ε/2:ℝ)))
  obtain ⟨D,hD⟩ := eventually_atTop.mp he
  refine ⟨max 40000 (max T D),le_max_left _ _,?_⟩
  intro H t hH hHt htH
  have hHT : T ≤ H := (le_max_left _ _).trans ((le_max_right _ _).trans hH)
  have hHD : D ≤ H := (le_max_right _ _).trans ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := by linarith
  have ht0 : 0 ≤ t := by linarith
  calc
    ‖riemannZeta (criticalPoint t)‖ < t^(1/6+ε/2:ℝ) := hlarge t (hHT.trans hHt)
    _ ≤ (2*H)^(1/6+ε/2:ℝ) := Real.rpow_le_rpow ht0 htH (by linarith)
    _ = (2:ℝ)^(1/6+ε/2:ℝ)*H^(1/6+ε/2:ℝ) := Real.mul_rpow (by norm_num) hH0.le
    _ ≤ H^(ε/2)*H^(1/6+ε/2:ℝ) := mul_le_mul_of_nonneg_right (hD H hHD) (by positivity)
    _ = H^(1/6+ε:ℝ) := by rw [← Real.rpow_add hH0]; congr 1; ring

end WeylPort
