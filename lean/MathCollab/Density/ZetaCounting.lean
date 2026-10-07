module
public import Mathlib.NumberTheory.LSeries.ZetaZeros
public import Mathlib.Tactic

@[expose] public section

open Filter Set
open scoped BigOperators Topology

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- Actual nontrivial zeros, with both edges of the critical strip excluded. -/
def IsNontrivialZetaZero (ρ : ℂ) : Prop :=
  riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- The natural analytic vanishing order; its finiteness and positivity at zeros
are proved below, so conversion from the extended natural order loses nothing. -/
def zetaMultiplicity (ρ : ℂ) : ℕ := analyticOrderNatAt riemannZeta ρ

theorem zeta_analyticOrder_ne_top {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  intro h
  have he := analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (show ρ ∈ ({1}ᶜ : Set ℂ) from hρ) (analyticOrderAt_eq_top.mp h)
  exact (riemannZeta_ne_zero_of_one_le_re (s := 2) (by norm_num)) (he (by simp))

theorem nontrivialZetaZero_ne_one {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) : ρ ≠ 1 := by
  intro he
  have := hρ.2.2
  simp [he] at this

theorem zetaMultiplicity_cast {ρ : ℂ} (hρ : ρ ≠ 1) :
    (zetaMultiplicity ρ : ℕ∞) = analyticOrderAt riemannZeta ρ :=
  Nat.cast_analyticOrderNatAt (zeta_analyticOrder_ne_top hρ)

theorem zetaMultiplicity_pos {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    0 < zetaMultiplicity ρ := by
  exact ENat.toNat_pos
    (analyticOrderAt_ne_zero.mpr ⟨analyticOn_riemannZeta ρ (nontrivialZetaZero_ne_one hρ), hρ.1⟩)
    (zeta_analyticOrder_ne_top (nontrivialZetaZero_ne_one hρ))

theorem zetaMultiplicity_local_factorization {ρ : ℂ} (hρ : IsNontrivialZetaZero ρ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g ρ ∧ g ρ ≠ 0 ∧
      ∀ᶠ z in 𝓝 ρ, riemannZeta z = (z-ρ)^(zetaMultiplicity ρ)*g z := by
  exact (analyticOn_riemannZeta ρ (nontrivialZetaZero_ne_one hρ)).analyticOrderAt_ne_top.mp
    (zeta_analyticOrder_ne_top (nontrivialZetaZero_ne_one hρ))

/-- Closed height and real-part cutoffs, inside the open critical strip. -/
def zetaZeroRegion (σ a b : ℝ) : Set ℂ :=
  {ρ | IsNontrivialZetaZero ρ ∧ σ ≤ ρ.re ∧ a ≤ ρ.im ∧ ρ.im ≤ b}

theorem zetaZeroRegion_finite (σ a b : ℝ) : (zetaZeroRegion σ a b).Finite := by
  refine ((isCompact_closedBall (0 : ℂ) (1+|a|+|b|)).inter_riemannZetaZeros_finite).subset ?_
  intro ρ hρ
  refine ⟨?_, hρ.1.1⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have him : |ρ.im| ≤ |a|+|b| := by
    have ha := neg_abs_le a
    have hb := le_abs_self b
    have ha0 := abs_nonneg a
    have hb0 := abs_nonneg b
    exact abs_le.mpr ⟨by linarith [hρ.2.2.1], by linarith [hρ.2.2.2]⟩
  calc
    ‖ρ‖ ≤ |ρ.re|+|ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
    _ ≤ 1+|a|+|b| := by rw [abs_of_pos hρ.1.2.1]; linarith [hρ.1.2.2]

/-- Every zero in the region, once as a location; multiplicity enters the sum. -/
def zetaZeroFinset (σ a b : ℝ) : Finset ℂ := (zetaZeroRegion_finite σ a b).toFinset

theorem mem_zetaZeroFinset {σ a b : ℝ} {ρ : ℂ} :
    ρ ∈ zetaZeroFinset σ a b ↔
      IsNontrivialZetaZero ρ ∧ σ ≤ ρ.re ∧ a ≤ ρ.im ∧ ρ.im ≤ b := by
  exact Set.Finite.mem_toFinset (zetaZeroRegion_finite σ a b)

/-- Count all actual zeros in the slab, with analytic multiplicity. -/
def zetaSlabCount (σ a b : ℝ) : ℕ :=
  ∑ ρ ∈ zetaZeroFinset σ a b, zetaMultiplicity ρ

/-- The packet's N(σ,T): both signs of the ordinate and both height endpoints. -/
def zetaDensityCount (σ T : ℝ) : ℕ := zetaSlabCount σ (-T) T

theorem mem_zetaDensityFinset {σ T : ℝ} {ρ : ℂ} :
    ρ ∈ zetaZeroFinset σ (-T) T ↔
      IsNontrivialZetaZero ρ ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T := by
  rw [mem_zetaZeroFinset, abs_le]

theorem zetaZeroFinset_card_le_count (σ a b : ℝ) :
    (zetaZeroFinset σ a b).card ≤ zetaSlabCount σ a b := by
  calc
    _ = ∑ _ρ ∈ zetaZeroFinset σ a b, 1 := by simp
    _ ≤ zetaSlabCount σ a b := Finset.sum_le_sum fun ρ hρ =>
      zetaMultiplicity_pos (mem_zetaZeroFinset.mp hρ).1

theorem zetaSlabCount_mono {σ σ' a a' b b' : ℝ}
    (hσ : σ' ≤ σ) (ha : a' ≤ a) (hb : b ≤ b') :
    zetaSlabCount σ a b ≤ zetaSlabCount σ' a' b' := by
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  obtain ⟨hz, hs, hlo, hhi⟩ := mem_zetaZeroFinset.mp hρ
  exact mem_zetaZeroFinset.mpr ⟨hz, hσ.trans hs, ha.trans hlo, hhi.trans hb⟩

theorem zetaDensityCount_mono {σ σ' T T' : ℝ} (hσ : σ' ≤ σ) (hT : T ≤ T') :
    zetaDensityCount σ T ≤ zetaDensityCount σ' T' :=
  zetaSlabCount_mono hσ (neg_le_neg hT) hT

end MathCollab.Density
