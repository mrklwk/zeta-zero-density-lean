module
public import MathCollab.Density.Packing

@[expose] public section

open Real Set
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

theorem localSet_localDiameter_le {H : ℝ} (hH : 1 ≤ H) (U : Finset ℝ) (j : ℤ) :
    localDiameter (localSet U H j) ≤ 4*H := by
  have hs : intervalSpan (localSet U H j) ≤ 3*H := by
    apply intervalSpan_le_of_forall (by positivity)
    intro t ht u hu
    exact (localSet_pair_distance ht hu).le
  dsimp [localDiameter]
  linarith

/-- Reflection stays in the same real length interval and uses the same original N. -/
theorem reflection_recursive_scale {N : ℕ} {T L H : ℝ}
    (hN : 0 < N) (_hT : 0 ≤ T) (hNL : (N : ℝ) ≤ L) (hH : 0 < H) (hHT : H ≤ T)
    {M : ℕ} (hM : M ∈ reflectionBlocks L H) :
    (N : ℝ) ≤ (N : ℝ)*M ∧ (N : ℝ)*M ≤ 8*(T+1) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 0 < L := hNp.trans_le hNL
  obtain ⟨hMp, _, hMhi⟩ := reflectionBlock_scale_bounds hL hH hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hMp
  refine ⟨by nlinarith, ?_⟩
  have hh := (le_div_iff₀ (by positivity : 0 < Real.pi*L)).1 hMhi
  have hi : (N : ℝ)*M*Real.pi ≤ 4*T := by
    have hc := mul_le_mul_of_nonneg_right hNL (show 0 ≤ (M : ℝ)*Real.pi by positivity)
    nlinarith
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hnm : 0 ≤ (N : ℝ)*M := by positivity
  have hc := mul_le_mul_of_nonneg_left hpi hnm
  nlinarith

theorem reflection_scale_error_power {T L : ℝ} (hT : 2 ≤ T)
    (hL : T^(1/3 : ℝ) ≤ L) : L^(-318 : ℝ) ≤ T^(-106 : ℝ) := by
  have hTp : 0 < T := by linarith
  have hp : 0 < T^(1/3 : ℝ) := Real.rpow_pos_of_pos hTp _
  have hh := Real.rpow_le_rpow_of_nonpos hp hL (by norm_num : (-318 : ℝ) ≤ 0)
  have he : (T^(1/3 : ℝ))^(-318 : ℝ) = T^(-106 : ℝ) := by
    rw [← Real.rpow_mul hTp.le]
    norm_num
  exact hh.trans_eq he

theorem reflection_error_specialization {T L r : ℝ} (hT : 2 ≤ T)
    (hL : T^(1/3 : ℝ) ≤ L) (hr : 0 ≤ r) (hrT : r ≤ T+1) :
    r^2*L^(-318 : ℝ) ≤ (9/4)*T^(-104 : ℝ) ∧
      r*L^(-318 : ℝ) ≤ (3/2)*T^(-105 : ℝ) := by
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := (Real.rpow_pos_of_pos hTp _).trans_le hL
  have hr' : r ≤ (3/2)*T := by linarith
  have hp := reflection_scale_error_power hT hL
  have he₂ : T^2*T^(-106 : ℝ) = T^(-104 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hTp]
    norm_num
  have he₁ : T*T^(-106 : ℝ) = T^(-105 : ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one T]
    rw [← Real.rpow_add hTp]
    norm_num
  constructor
  · calc
      _ ≤ ((3/2)*T)^2*T^(-106 : ℝ) :=
        mul_le_mul (by nlinarith) hp (Real.rpow_nonneg hLp.le _) (sq_nonneg _)
      _ = (9/4)*(T^2*T^(-106 : ℝ)) := by ring
      _ = _ := by rw [he₂]
  · calc
      _ ≤ ((3/2)*T)*T^(-106 : ℝ) :=
        mul_le_mul hr' hp (Real.rpow_nonneg hLp.le _) (by positivity)
      _ = (3/2)*(T*T^(-106 : ℝ)) := by ring
      _ = _ := by rw [he₁]

/-- The paper's uniform T-error contract is a consequence of the proved reflection theorem. -/
theorem uniform_reflection_application (w : ReflectionCutoff) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (T L H : ℝ) (U : Finset ℝ),
      2 ≤ T → T^(1/3 : ℝ) ≤ L → 0 < H → oneSeparated U → intervalSpan U ≤ T →
      shellEnergy w L H U ≤
        (20000/Real.pi^2)*(mellinMass w)^2*(L^2/H)*localReflectionEnergy L H U +
          E*T^(-100 : ℝ) ∧
      (∑ _t ∈ U, ‖hKernel w L 0‖^2) ≤ E*T^(-100 : ℝ) := by
  obtain ⟨K, hK, hbound⟩ := uniform_reflection w (A := 160) (by norm_num)
  refine ⟨9*K^2, by positivity, ?_⟩
  intro T L H U hT hL hH hsep hdiam
  have hTp : 0 < T := by linarith
  have hLp : 0 < L := (Real.rpow_pos_of_pos hTp _).trans_le hL
  have hc : (U.card : ℝ) ≤ T+1 := by
    have hh := separated_card_le_localDiameter hsep
    dsimp [localDiameter] at hh
    linarith
  have he := reflection_error_specialization hT hL (Nat.cast_nonneg U.card) hc
  have hb := hbound L H U hLp hH
  have hexp : (2-2*(160 : ℝ)) = -318 := by norm_num
  simp only [Nat.cast_ofNat, hexp] at hb
  have hpow₂ : T^(-104 : ℝ) ≤ T^(-100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hpow₁ : T^(-105 : ℝ) ≤ T^(-100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have he₂ : 4*K^2*(U.card : ℝ)^2*L^(-318 : ℝ) ≤ 9*K^2*T^(-100 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left he.1 (show 0 ≤ 4*K^2 by positivity)
    have hi := mul_le_mul_of_nonneg_left hpow₂ (show 0 ≤ 9*K^2 by positivity)
    nlinarith
  have he₁ : K^2*(U.card : ℝ)*L^(-318 : ℝ) ≤ 9*K^2*T^(-100 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left he.2 (sq_nonneg K)
    have hi := mul_le_mul_of_nonneg_left hpow₁ (show 0 ≤ (3/2)*K^2 by positivity)
    have hn := Real.rpow_nonneg hTp.le (-100)
    nlinarith [mul_nonneg (sq_nonneg K) hn]
  exact ⟨hb.1.trans (add_le_add le_rfl he₂), hb.2.trans he₁⟩

end MathCollab.Density
