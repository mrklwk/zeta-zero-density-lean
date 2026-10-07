module
public import WeylPort.AFE.AFESecondLimits
public import WeylPort.AFE.UniformCoefficients
public import WeylPort.GapSum
public import WeylPort.Reflection
public import WeylPort.CutoffSelection

@[expose] public section

namespace WeylPort
open DhimanKadiriQuesadaHerrera2026
open scoped Topology

/-- A fixed majorant for the left endpoint in the critical-line Poisson formula. -/
noncomputable def criticalPoissonConstant : ℝ :=
  (Real.log 2+1)/(2*Real.pi) +
  (1+2*Real.pi)/(4*Real.pi^2)*(Real.pi/2+Real.log 2) +
  (2*(1+2*Real.pi))/(4*Real.pi^3)*9 +
  (1+2*Real.pi)/(4*Real.pi^3)*17

theorem criticalPoissonConstant_pos : 0 < criticalPoissonConstant := by
  unfold criticalPoissonConstant
  have : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- The source's actual Poisson error is uniformly bounded under the repaired gaps. -/
theorem afeSecondLeftError_critical_uniform {x y : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x)
    (hgap : 1/2 ≤ (⌊y⌋₊:ℝ)+1-y) :
    afeSecondLeftError (1/2) (x*y) x ≤ criticalPoissonConstant := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hc0 : 0 ≤ x*y := by positivity
  have hcancel : x*y/x = y := by field_simp
  have hgaphi : (⌊y⌋₊:ℝ)+1-y ≤ 1 := by linarith [Nat.floor_le hy0.le]
  have hplus := plus_coefficients_uniform hy
  have hminus := minus_coefficients_uniform hy hgap hgaphi
  have hsq : minusSquareBound ⌊y⌋₊ y + plusSquareBound y ≤ 9/y := by
    calc
      _ ≤ 7/y+2/y := add_le_add hminus.1 hplus.1
      _ = _ := by ring
  have hcube : minusCubeBound ⌊y⌋₊ y + plusCubeBound y ≤ 17/y := by
    calc
      _ ≤ 15/y+2/y := add_le_add hminus.2 hplus.2
      _ = _ := by ring
  let K := 1+2*Real.pi
  let H := secondH (afePhase (x*y)) (afeWeight (1/2)) x
  let H1 := secondH1 (afePhase (x*y)) (afeWeight (1/2)) x
  have hK : 0 < K := by dsimp [K]; positivity
  have hH0 : 0 ≤ H := secondH_nonneg _ _ _
  have hH10 : 0 ≤ H1 := secondH1_nonneg _ _ _
  have hw0 : 0 ≤ x^(-(1/2:ℝ)) := Real.rpow_nonneg hx0.le _
  have hw1 : x^(-(1/2:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hH : H/y ≤ K := by
    dsimp [H]
    rw [secondH_afe (by norm_num) hc0 hx0, Real.rpow_sub_one hx0.ne']
    have hb : ((1/2:ℝ)+2*Real.pi*(x*y)) * (x^(-(1/2:ℝ))/x) ≤
        ((1/2:ℝ)+2*Real.pi*(x*y))/x := by
      calc
        _ ≤ ((1/2:ℝ)+2*Real.pi*(x*y)) * (1/x) := by gcongr
        _ = _ := by ring
    apply (div_le_div_of_nonneg_right hb hy0.le).trans
    dsimp [K]
    apply (div_le_iff₀ hy0).mpr
    apply (div_le_iff₀ hx0).mpr
    nlinarith [mul_le_mul hx hy (by norm_num : (0:ℝ) ≤ 1) hx0.le]
  have hH1id : H1 = (3/2:ℝ)*H/x := by
    dsimp [H1,H]
    rw [secondH1_afe (by norm_num) hc0 hx0, secondH_afe (by norm_num) hc0 hx0]
    rw [show -(1/2:ℝ)-2 = (-(1/2:ℝ)-1)-1 by ring, Real.rpow_sub_one hx0.ne']
    ring
  have hH1 : H1/y ≤ 2*K := by
    rw [hH1id]
    have hid : (3/2:ℝ)*H/x/y = (3/2:ℝ)*(H/y)/x := by ring
    rw [hid]
    calc
      _ ≤ (3/2:ℝ)*K/x := by gcongr
      _ ≤ (3/2:ℝ)*K := div_le_self (by positivity) hx
      _ ≤ 2*K := by nlinarith
  have hHx : (H*((x*y)/x^2))/y ≤ K := by
    have he : (H*((x*y)/x^2))/y = (H/y)*(y/x) := by field_simp
    rw [he]
    have hr : y/x ≤ 1 := (div_le_one hx0).mpr hyx
    calc
      _ ≤ K*1 := mul_le_mul hH hr (by positivity) hK.le
      _ = K := mul_one K
  have hb1 : x^(-(1/2:ℝ))/(2*Real.pi)*(Real.log 2+1/y) ≤ (Real.log 2+1)/(2*Real.pi) := by
    have hi : 1/y ≤ 1 := (div_le_one hy0).mpr hy
    calc
      _ ≤ 1/(2*Real.pi)*(Real.log 2+1) := by gcongr
      _ = _ := by ring
  have hb2 : H/(4*Real.pi^2)*((Real.pi/2+Real.log 2)/y) ≤ K/(4*Real.pi^2)*(Real.pi/2+Real.log 2) := by
    rw [show H/(4*Real.pi^2)*((Real.pi/2+Real.log 2)/y) = (H/y)/(4*Real.pi^2)*(Real.pi/2+Real.log 2) by ring]
    gcongr
  have hb3 : H1/(4*Real.pi^3)*(minusSquareBound ⌊y⌋₊ y+plusSquareBound y) ≤ (2*K)/(4*Real.pi^3)*9 := by
    calc
      _ ≤ H1/(4*Real.pi^3)*(9/y) := by gcongr
      _ = (H1/y)/(4*Real.pi^3)*9 := by ring
      _ ≤ _ := by gcongr
  have hb4 : H*((x*y)/x^2)/(4*Real.pi^3)*(minusCubeBound ⌊y⌋₊ y+plusCubeBound y) ≤ K/(4*Real.pi^3)*17 := by
    calc
      _ ≤ H*((x*y)/x^2)/(4*Real.pi^3)*(17/y) := by gcongr
      _ = (H*((x*y)/x^2)/y)/(4*Real.pi^3)*17 := by ring
      _ ≤ _ := by gcongr
  unfold afeSecondLeftError criticalPoissonConstant
  simp only [hcancel, afeWeight]
  change _ ≤ (Real.log 2+1)/(2*Real.pi) + K/(4*Real.pi^2)*(Real.pi/2+Real.log 2) + (2*K)/(4*Real.pi^3)*9 + K/(4*Real.pi^3)*17
  exact add_le_add (add_le_add (add_le_add hb1 hb2) hb3) hb4

/-- The pole and lower-integral boundary factors are uniformly small. -/
theorem critical_boundary_factors {x y t : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hscale : 2*Real.pi*x*y = t) (N : ℕ) (hN : (N:ℝ) ≤ y) :
    (x/t)*x^(-(1/2:ℝ)) ≤ 1 ∧
    x^(1-(1/2:ℝ))/t ≤ 1 ∧
    (2*Real.pi*x^(2-(1/2:ℝ))/t^2)*(((N:ℝ)+1)/2) ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hp : 0 < Real.pi := Real.pi_pos
  have hden : 1 ≤ 2*Real.pi*y := by nlinarith [Real.pi_gt_three]
  have hw : x^(-(1/2:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx (by norm_num)
  have hw0 : 0 ≤ x^(-(1/2:ℝ)) := by positivity
  have hi : 1/(2*Real.pi*y) ≤ 1 := (div_le_one (by positivity)).mpr hden
  have hbound : x^(-(1/2:ℝ))/(2*Real.pi*y) ≤ 1 :=
    (div_le_one (by positivity)).mpr (hw.trans hden)
  have hp1 : x^(1-(1/2:ℝ)) = x*x^(-(1/2:ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
  have hp2 : x^(2-(1/2:ℝ)) = x^2*x^(-(1/2:ℝ)) := by
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_two]
  have he1 : (x/t)*x^(-(1/2:ℝ)) = x^(-(1/2:ℝ))/(2*Real.pi*y) := by
    rw [← hscale]; field_simp
  have he2 : x^(1-(1/2:ℝ))/t = x^(-(1/2:ℝ))/(2*Real.pi*y) := by
    rw [hp1, ← hscale]; field_simp
  refine ⟨he1.trans_le hbound, he2.trans_le hbound, ?_⟩
  have he3 : (2*Real.pi*x^(2-(1/2:ℝ))/t^2)*(((N:ℝ)+1)/2) =
      x^(-(1/2:ℝ))*(((N:ℝ)+1)/(4*Real.pi*y^2)) := by
    rw [hp2, ← hscale]; field_simp; ring
  rw [he3]
  have hr : ((N:ℝ)+1)/(4*Real.pi*y^2) ≤ 1 := by
    calc
      _ ≤ (2*y)/(4*Real.pi*y^2) := by gcongr; linarith
      _ = 1/(2*Real.pi*y) := by field_simp; norm_num
      _ ≤ 1 := hi
  exact (mul_le_mul hw hr (by positivity) (by norm_num : (0:ℝ) ≤ 1)).trans (by norm_num)

/-- The lower oscillatory integral sum has a constant bound with only the first cutoff half-integral. -/
theorem norm_critical_lower_integrals_uniform {x y t : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x) (ht : 0 ≤ t)
    (hscale : 2*Real.pi*x*y = t) (k : ℤ) (hxk : x = (k:ℝ)+1/2)
    (hgap : (⌊y⌋₊:ℝ)+1/8 ≤ y) :
    ‖∑ m ∈ Finset.Icc 1 ⌊y⌋₊,
      weightedIntegral ((1/2:ℂ)+(t:ℂ)*Complex.I) 0 x (m:ℝ)‖ ≤ 2+24/Real.pi := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hN : (⌊y⌋₊:ℝ) ≤ y := Nat.floor_le hy0.le
  have hb := critical_boundary_factors hx hy hscale ⌊y⌋₊ hN
  have hi := norm_sum_lower_integral_le_arithmetic (σ := (1/2:ℝ))
    (by norm_num) hx0 hy0 (by rwa [abs_of_nonneg ht]) k hxk ⌊y⌋₊ (by linarith)
  norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hi
  rw [abs_of_nonneg ht] at hi
  have hg := quadratic_gap_sum_le y ⌊y⌋₊ hy hgap
  have hthird : x^(-(1/2:ℝ))/Real.pi *
      (∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m:ℝ)^2/(y^2*(y-m))) ≤ 24/Real.pi := by
    calc
      _ ≤ x^(-(1/2:ℝ))/Real.pi * (8*(1+Real.log y)) := by gcongr
      _ = (8/Real.pi)*(x^(-(1/2:ℝ))*(1+Real.log y)) := by ring
      _ ≤ (8/Real.pi)*3 := by gcongr; exact weighted_log_cutoff_le hx hy hyx
      _ = _ := by ring
  linarith [hb.2.1, hb.2.2]

noncomputable def criticalAFEConstant : ℝ :=
  criticalPoissonConstant + 3 + 24/Real.pi + 1/(1-Real.exp (-Real.pi))

theorem criticalAFEConstant_pos : 0 < criticalAFEConstant := by
  have he : Real.exp (-Real.pi) < 1 := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  unfold criticalAFEConstant
  have := criticalPoissonConstant_pos
  positivity

theorem norm_chi_criticalPoint (t : ℝ) : ‖chi (criticalPoint t)‖ = 1 := by
  exact norm_critical_chi_product t

/-- A bounded error for the actual zeta AFE, with an unrestricted dual cutoff. -/
theorem norm_critical_afe_uniform {x y t : ℝ}
    (hx : 1 ≤ x) (hy : 1 ≤ y) (hyx : y ≤ x) (ht : 1 ≤ t)
    (hscale : 2*Real.pi*x*y = t) (k : ℤ) (hxk : x = (k:ℝ)+1/2)
    (hgaplo : (⌊y⌋₊:ℝ)+1/8 ≤ y) (hgaphi : y ≤ (⌊y⌋₊:ℝ)+1/2)
    (henv : Real.exp (-Real.pi*t)*(t^2+1) ≤ 1) :
    ‖afeRemainder (criticalPoint t) x y‖ ≤ criticalAFEConstant := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have ht0 : 0 < t := by linarith
  have hc : t/(2*Real.pi) = x*y := by rw [← hscale]; field_simp
  have hcancel : x*y/x = y := by field_simp
  have hσ : (1/2:ℝ) ∈ Set.Ioo 0 1 := by norm_num
  have hgap : 1/2 ≤ (⌊y⌋₊:ℝ)+1-y := by linarith
  let s := criticalPoint t
  let B : ℂ := (x:ℂ)^(1-s)/(s-1)
  let F : ℂ := ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail s x (m:ℝ)
  let F0 : ℂ := ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegralTail s 0 (m:ℝ)
  let L : ℂ := ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, weightedIntegral s 0 x (m:ℝ)
  let Q : ℂ := chi s * ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (m:ℂ)^(s-1)
  have hp : ‖riemannZeta s-sharpZetaSum s x-B-F‖ ≤ criticalPoissonConstant := by
    have h := afe_zeta_sub_sum_pole_integrals_bound hσ ht0 hx0 ⟨k,hxk⟩
      (by simpa only [hc,hcancel] using hgap)
    simp only [hc,hcancel] at h
    have hh := h.trans (afeSecondLeftError_critical_uniform hx hy hyx hgap)
    simpa only [B,F,s,criticalPoint,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hh
  have hb : ‖B‖ ≤ 1 := by
    have h := norm_afe_pole_le (sigma := (1/2:ℝ)) ht0 hx0
    have hh := h.trans (critical_boundary_factors hx hy hscale ⌊y⌋₊ (Nat.floor_le hy0.le)).1
    simpa only [B,s,criticalPoint,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using hh
  have hl : ‖L‖ ≤ 2+24/Real.pi := by
    exact norm_critical_lower_integrals_uniform hx hy hyx ht0.le hscale k hxk hgaplo
  have he : F = F0-L := by
    dsimp only [F,F0,L]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    have hm0 : 0 < (m:ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    simpa only [s,criticalPoint,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      weightedIntegralTail_eq_sub (t := t) hσ hm0 x
  have hyT : y ≤ t := by
    rw [← hscale]
    have hp : 1 ≤ 2*Real.pi*x := by nlinarith [Real.pi_gt_three]
    nlinarith
  have hpoly : y^(1/2:ℝ)*Real.log y+1 ≤ t^2+1 := by
    have hs : y^(1/2:ℝ) ≤ y := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hy (by norm_num : (1/2:ℝ) ≤ 1)
    have hlog : Real.log y ≤ y := (Real.log_le_sub_one_of_pos hy0).trans (by linarith)
    have hmul := mul_le_mul hs hlog (Real.log_nonneg hy) hy0.le
    nlinarith
  have hd : 0 < 1-Real.exp (-Real.pi) := by
    have := Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos] : -Real.pi < 0)
    linarith
  have hg : ‖F0-Q‖ ≤ 1/(1-Real.exp (-Real.pi)) := by
    have h := norm_sum_weightedIntegralTail_sub_chi_le (t := t) (t₀ := 1) hσ hy (by norm_num)
      (by rwa [abs_of_pos ht0])
    norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat,mul_one] at h
    change ‖F0-Q‖ ≤ ‖chi (criticalPoint t)‖ *
      (Real.exp (-Real.pi*t)/(1-Real.exp (-Real.pi)))*(y^(1/2:ℝ)*Real.log y+1) at h
    rw [norm_chi_criticalPoint,one_mul] at h
    apply h.trans
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hd.le
    exact (mul_le_mul_of_nonneg_left hpoly (Real.exp_nonneg _)).trans henv
  have htail : ‖F-Q‖ ≤ 1/(1-Real.exp (-Real.pi))+(2+24/Real.pi) := by
    rw [he,sub_right_comm]
    exact (norm_sub_le _ _).trans (add_le_add hg hl)
  have hid : afeRemainder s x y =
      (riemannZeta s-sharpZetaSum s x-B-F)+B+(F-Q) := by
    dsimp only [afeRemainder,Q,sharpZetaSum,zetaTerm]
    simp only [neg_sub]
    ring
  rw [hid]
  have h := (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add hp hb)) htail)
  apply h.trans
  unfold criticalAFEConstant
  ring_nf
  exact le_rfl

/-- Suitable short AFE cutoffs and a fixed actual-zeta remainder bound hold at every sufficiently large height. -/
theorem eventually_actual_zeta_short_afe :
    ∀ᶠ t : ℝ in Filter.atTop, ∃ A M : ℕ,
      (A:ℝ)^2 ≤ t ∧ (M:ℝ)^2 ≤ t ∧
      ‖afeRemainder (criticalPoint t) ((A:ℝ)+1/2) (t/(2*Real.pi*((A:ℝ)+1/2)))‖ ≤ criticalAFEConstant ∧
      ⌊t/(2*Real.pi*((A:ℝ)+1/2))⌋₊ = M := by
  filter_upwards [Filter.eventually_ge_atTop (200*Real.pi), eventually_gamma_envelope_le_one] with t ht he
  obtain ⟨A,M,hx,hy,hscale,hfx,hfy,hlo,hhi,hA,hM,hxR,hxR',hyR,hyR'⟩ := exists_afe_cutoffs_all_heights t ht
  refine ⟨A,M,hA,hM,?_,hfy⟩
  apply norm_critical_afe_uniform hx hy (hyR'.trans hxR) (by nlinarith [Real.pi_gt_three]) hscale (A:ℤ)
  · simp
  · simpa only [hfy] using hlo
  · simpa only [hfy] using hhi
  · exact he

end WeylPort
