module
public import MathCollab.Density.Oscillatory
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open Real Complex Set MeasureTheory
open scoped ContDiff

noncomputable section
namespace MathCollab.Density

/-- Reciprocal normalized logarithmic phase derivative. -/
def phaseQuotient (p : ℝ × ℝ) (x : ℝ) : ℂ :=
  ((x / (p.1 - p.2 * x) : ℝ) : ℂ)

/-- Repeated integration-by-parts amplitudes; no decay estimate is assumed. -/
def ibpAmplitude (w : ℝ → ℂ) : ℕ → (ℝ × ℝ) → ℝ → ℂ
  | 0, _, x => w x
  | n + 1, p, x => deriv (fun y => ibpAmplitude w n p y * phaseQuotient p y) x

theorem phaseQuotient_contDiffAt {p : ℝ × ℝ} {x : ℝ}
    (h : p.1 - p.2 * x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => phaseQuotient z.1 z.2) (p, x) := by
  unfold phaseQuotient
  apply Complex.ofRealCLM.contDiff.contDiffAt.comp
  exact contDiffAt_snd.div
    ((contDiffAt_fst.fst).sub (contDiffAt_fst.snd.mul contDiffAt_snd)) h

theorem ibpAmplitude_contDiffAt {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (n : ℕ) {p : ℝ × ℝ} {x : ℝ} (h : p.1 - p.2 * x ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => ibpAmplitude w n z.1 z.2) (p, x) := by
  induction n generalizing p x with
  | zero => exact hw.contDiffAt.comp _ contDiffAt_snd
  | succ n ih =>
    have hg : ContDiffAt ℝ ∞
        (fun z : (ℝ × ℝ) × ℝ => ibpAmplitude w n z.1 z.2 * phaseQuotient z.1 z.2)
        (p, x) := (ih h).mul (phaseQuotient_contDiffAt h)
    have hf : ContDiffAt ℝ ∞
        (Function.uncurry (fun z : (ℝ × ℝ) × ℝ =>
          fun y : ℝ => ibpAmplitude w n z.1 y * phaseQuotient z.1 y))
        ((p, x), x) := by
      convert hg.comp ((p, x), x) (show ContDiffAt ℝ ∞
        (fun z : ((ℝ × ℝ) × ℝ) × ℝ => (z.1.1, z.2)) ((p, x), x) from
          contDiffAt_fst.fst.prodMk contDiffAt_snd) using 1
      rfl
    have hd := hf.fderiv (m := ∞) (g := fun z : (ℝ × ℝ) × ℝ => z.2)
      contDiffAt_snd (by simp)
    exact hd.clm_apply contDiffAt_const

theorem ibpAmplitude_tsupport_subset (w : ℝ → ℂ) (n : ℕ) (p : ℝ × ℝ) :
    tsupport (ibpAmplitude w n p) ⊆ tsupport w := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
    exact tsupport_deriv_subset.trans (tsupport_mul_subset_left.trans ih)

/-- Fixed compact parameter set with a uniform denominator gap on an enlarged support. -/
def offBandParameters : Set (ℝ × ℝ) :=
  {p | |p.1| ≤ 2 ∧ |p.2| ≤ 2 * Real.pi ∧
    ∀ x ∈ Icc (1 / 3 : ℝ) 6, (1 / 300 : ℝ) ≤ |p.1 - p.2 * x|}

theorem offBandParameters_isCompact : IsCompact offBandParameters := by
  have hclosed : IsClosed offBandParameters := by
    apply IsClosed.inter
    · exact isClosed_le (continuous_fst.abs) continuous_const
    · apply IsClosed.inter
      · exact isClosed_le (continuous_snd.abs) continuous_const
      · have heq : {p : ℝ × ℝ | ∀ x ∈ Icc (1 / 3 : ℝ) 6,
              (1 / 300 : ℝ) ≤ |p.1 - p.2 * x|} =
            ⋂ (x : ℝ) (_ : x ∈ Icc (1 / 3 : ℝ) 6),
              {p : ℝ × ℝ | (1 / 300 : ℝ) ≤ |p.1 - p.2 * x|} := by
          ext p
          simp
        change IsClosed {p : ℝ × ℝ | ∀ x ∈ Icc (1 / 3 : ℝ) 6,
          (1 / 300 : ℝ) ≤ |p.1 - p.2 * x|}
        rw [heq]
        exact isClosed_biInter fun (x : ℝ) (_ : x ∈ Icc (1 / 3 : ℝ) 6) =>
          isClosed_le continuous_const ((continuous_fst.sub (continuous_snd.mul_const x)).abs)
  apply ((isCompact_Icc : IsCompact (Icc (-2 : ℝ) 2)).prod
    (isCompact_Icc : IsCompact (Icc (-2 * Real.pi) (2 * Real.pi)))).of_isClosed_subset hclosed
  intro p hp
  refine ⟨abs_le.mp hp.1, ?_⟩
  constructor
  · nlinarith [(abs_le.mp hp.2.1).1]
  · exact (abs_le.mp hp.2.1).2

theorem ibpAmplitude_uniform_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ offBandParameters, ∀ x ∈ Icc (1 / 3 : ℝ) 6,
      ‖ibpAmplitude w n p x‖ ≤ C := by
  have hcont : ContinuousOn
      (fun z : (ℝ × ℝ) × ℝ => ‖ibpAmplitude w n z.1 z.2‖)
      (offBandParameters ×ˢ Icc (1 / 3 : ℝ) 6) := by
    intro z hz
    have hgap := hz.1.2.2 z.2 hz.2
    have hne : z.1.1 - z.1.2 * z.2 ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero] at hgap
      norm_num at hgap
    exact (ibpAmplitude_contDiffAt hw n hne).continuousAt.norm.continuousWithinAt
  obtain ⟨C, hC⟩ := (offBandParameters_isCompact.prod isCompact_Icc).bddAbove_image hcont
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp x hx
  exact (hC ⟨(p, x), ⟨hp, hx⟩, rfl⟩).trans (le_max_left _ _)

/-- A uniform gap on a slightly enlarged interval around the cutoff support. -/
theorem offBand_denominator_gap {H v k x : ℝ} (hH : 0 < H)
    (hv : H ≤ v) (hv2 : v ≤ 2 * H) (hx : x ∈ Icc (1 / 3 : ℝ) 6)
    (hk : k < H / (20 * Real.pi) ∨ 4 * H / Real.pi < k) :
    (H + |k|) / 300 ≤ |v - 2 * Real.pi * k * x| := by
  have hp := Real.pi_gt_three
  have hp4 := Real.pi_lt_four
  have hx0 : 0 ≤ x := by linarith [hx.1]
  by_cases hk0 : k ≤ 0
  · rw [abs_of_nonpos hk0]
    have hprod : 2 * Real.pi * (-k) * (1 / 3) ≤ 2 * Real.pi * (-k) * x :=
      mul_le_mul_of_nonneg_left hx.1 (mul_nonneg (by positivity) (neg_nonneg.mpr hk0))
    have hpk : 3 * (-k) ≤ Real.pi * (-k) :=
      mul_le_mul_of_nonneg_right hp.le (by linarith)
    have hsign : 0 ≤ v - 2 * Real.pi * k * x := by nlinarith
    rw [abs_of_nonneg hsign]
    nlinarith
  · have hkpos : 0 < k := lt_of_not_ge hk0
    rw [abs_of_pos hkpos]
    rcases hk with hlo | hhi
    · have hsmall : k * (20 * Real.pi) < H := (lt_div_iff₀ (by positivity)).1 hlo
      have hprod : 2 * Real.pi * k * x ≤ 2 * Real.pi * k * 6 :=
        mul_le_mul_of_nonneg_left hx.2 (by positivity)
      have hpk : 3 * k ≤ Real.pi * k := mul_le_mul_of_nonneg_right hp.le hkpos.le
      have hsign : 0 ≤ v - 2 * Real.pi * k * x := by nlinarith
      rw [abs_of_nonneg hsign]
      nlinarith
    · have hlarge : 4 * H < k * Real.pi := (div_lt_iff₀ Real.pi_pos).1 hhi
      have hprod : 2 * Real.pi * k * (1 / 3) ≤ 2 * Real.pi * k * x :=
        mul_le_mul_of_nonneg_left hx.1 (by positivity)
      have hpk : 3 * k ≤ Real.pi * k := mul_le_mul_of_nonneg_right hp.le hkpos.le
      have hpk4 : Real.pi * k ≤ 4 * k := mul_le_mul_of_nonneg_right hp4.le hkpos.le
      have hsign : v - 2 * Real.pi * k * x ≤ 0 := by nlinarith
      rw [abs_of_nonpos hsign]
      nlinarith

/-- The normalized parameters lie in one compact set, independently of all scales. -/
theorem normalized_offBand_mem {H v k : ℝ} (hH : 0 < H)
    (hv : H ≤ v) (hv2 : v ≤ 2 * H)
    (hk : k < H / (20 * Real.pi) ∨ 4 * H / Real.pi < k) :
    (v / (H + |k|), (2 * Real.pi * k) / (H + |k|)) ∈ offBandParameters := by
  have hR : 0 < H + |k| := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_div, abs_of_pos hR, abs_of_pos (hH.trans_le hv)]
    apply (div_le_iff₀ hR).2
    nlinarith [abs_nonneg k]
  · rw [abs_div, abs_of_pos hR, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
    apply (div_le_iff₀ hR).2
    nlinarith [Real.pi_pos]
  · intro x hx
    change (1 / 300 : ℝ) ≤ |v / (H + |k|) - (2 * Real.pi * k) / (H + |k|) * x|
    rw [div_mul_eq_mul_div, ← sub_div, abs_div, abs_of_pos hR]
    apply (le_div_iff₀ hR).2
    have hg := offBand_denominator_gap hH hv hv2 hx hk
    linarith

/-- The normalized logarithmic phase, with the large scale kept separate. -/
def logOscillation (R : ℝ) (p : ℝ × ℝ) (x : ℝ) : ℂ :=
  Complex.exp (((R * (p.1 * Real.log x - p.2 * x) : ℝ) : ℂ) * Complex.I)

theorem norm_logOscillation (R : ℝ) (p : ℝ × ℝ) (x : ℝ) :
    ‖logOscillation R p x‖ = 1 := by
  simp [logOscillation, Complex.norm_exp]

theorem hasDerivAt_logOscillation (R : ℝ) (p : ℝ × ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (logOscillation R p)
      (((R * (p.1 / x - p.2) : ℝ) : ℂ) * Complex.I * logOscillation R p x) x := by
  have hr : HasDerivAt (fun y : ℝ => R * (p.1 * Real.log y - p.2 * y))
      (R * (p.1 / x - p.2)) x := by
    convert (((Real.hasDerivAt_log hx).const_mul p.1).sub
      ((hasDerivAt_id x).const_mul p.2)).const_mul R using 1
    · rfl
    · simp only [div_eq_mul_inv, mul_one]
  convert (hr.ofReal_comp.mul_const Complex.I).cexp using 1
  · rfl
  · dsimp [logOscillation]
    ring

theorem ibpAmplitude_contDiffAt_slice {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (n : ℕ) {p : ℝ × ℝ} {x : ℝ} (h : p.1 - p.2 * x ≠ 0) :
    ContDiffAt ℝ ∞ (ibpAmplitude w n p) x := by
  convert (ibpAmplitude_contDiffAt hw n h).comp x
    (contDiffAt_const.prodMk contDiffAt_id) using 1
  rfl

theorem phaseQuotient_contDiffAt_slice {p : ℝ × ℝ} {x : ℝ}
    (h : p.1 - p.2 * x ≠ 0) : ContDiffAt ℝ ∞ (phaseQuotient p) x := by
  convert (phaseQuotient_contDiffAt h).comp x
    (contDiffAt_const.prodMk contDiffAt_id) using 1
  rfl

theorem offBandParameters_ne {p : ℝ × ℝ} (hp : p ∈ offBandParameters)
    {x : ℝ} (hx : x ∈ Icc (1 / 3 : ℝ) 6) : p.1 - p.2 * x ≠ 0 := by
  have hh := hp.2.2 x hx
  intro hzero
  rw [hzero, abs_zero] at hh
  norm_num at hh

def ibpIntegral (w : ℝ → ℂ) (R : ℝ) (p : ℝ × ℝ) (n : ℕ) : ℂ :=
  ∫ x in (1 / 3 : ℝ)..6, ibpAmplitude w n p x * logOscillation R p x

/-- Exact one-step integration by parts, with vanishing endpoint amplitudes. -/
theorem ibpIntegral_recurrence {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5)
    {p : ℝ × ℝ} (hp : p ∈ offBandParameters) (R : ℝ) (n : ℕ) :
    ((R : ℂ) * Complex.I) * ibpIntegral w R p n = -ibpIntegral w R p (n + 1) := by
  let g : ℝ → ℂ := fun x => ibpAmplitude w n p x * phaseQuotient p x
  have hg : ∀ x ∈ uIcc (1 / 3 : ℝ) 6,
      HasDerivAt g (ibpAmplitude w (n + 1) p x) x := by
    intro x hx
    have hx' : x ∈ Icc (1 / 3 : ℝ) 6 := by simpa only [uIcc_of_le (by norm_num : (1 / 3 : ℝ) ≤ 6)] using hx
    exact ((ibpAmplitude_contDiffAt_slice hw n (offBandParameters_ne hp hx')).mul
      (phaseQuotient_contDiffAt_slice (offBandParameters_ne hp hx'))).differentiableAt
        (by simp) |>.hasDerivAt
  have he : ∀ x ∈ uIcc (1 / 3 : ℝ) 6,
      HasDerivAt (logOscillation R p)
        (((R * (p.1 / x - p.2) : ℝ) : ℂ) * Complex.I * logOscillation R p x) x := by
    intro x hx
    have hx' : x ∈ Icc (1 / 3 : ℝ) 6 := by simpa only [uIcc_of_le (by norm_num : (1 / 3 : ℝ) ≤ 6)] using hx
    exact hasDerivAt_logOscillation R p (by linarith [hx'.1])
  have hgi : IntervalIntegrable (ibpAmplitude w (n + 1) p) volume (1 / 3) 6 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx' : x ∈ Icc (1 / 3 : ℝ) 6 := by simpa only [uIcc_of_le (by norm_num : (1 / 3 : ℝ) ≤ 6)] using hx
    exact (ibpAmplitude_contDiffAt_slice hw (n+1) (offBandParameters_ne hp hx')).continuousAt.continuousWithinAt
  have hei : IntervalIntegrable
      (fun x : ℝ => ((R * (p.1 / x - p.2) : ℝ) : ℂ) * Complex.I * logOscillation R p x)
      volume (1 / 3) 6 := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx' : x ∈ Icc (1 / 3 : ℝ) 6 := by simpa only [uIcc_of_le (by norm_num : (1 / 3 : ℝ) ≤ 6)] using hx
    have hx0 : x ≠ 0 := by linarith [hx'.1]
    apply ContinuousAt.continuousWithinAt
    exact ((Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_const.mul ((continuousAt_const.div continuousAt_id hx0).sub continuousAt_const))).mul
        continuousAt_const).mul (hasDerivAt_logOscillation R p hx0).continuousAt
  have hend : g (1 / 3) = 0 ∧ g 6 = 0 := by
    have hz (x : ℝ) (hx : x ∉ Icc (1 / 2 : ℝ) 5) : g x = 0 := by
      have hnot : x ∉ tsupport (ibpAmplitude w n p) :=
        fun hh => hx (hws (ibpAmplitude_tsupport_subset w n p hh))
      simp only [g, image_eq_zero_of_notMem_tsupport hnot, zero_mul]
    exact ⟨hz _ (by norm_num), hz _ (by norm_num)⟩
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hg he hgi hei
  rw [hend.1, hend.2, zero_mul, zero_mul, sub_self, zero_sub] at hparts
  calc
    ((R : ℂ) * Complex.I) * ibpIntegral w R p n =
        ∫ x in (1 / 3 : ℝ)..6, g x *
          (((R * (p.1 / x - p.2) : ℝ) : ℂ) * Complex.I * logOscillation R p x) := by
      rw [ibpIntegral, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : x ∈ Icc (1 / 3 : ℝ) 6 := by simpa only [uIcc_of_le (by norm_num : (1 / 3 : ℝ) ≤ 6)] using hx
      have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hx'.1])
      have hd : (p.1 : ℂ) - (p.2 : ℂ) * (x : ℂ) ≠ 0 := by
        exact_mod_cast offBandParameters_ne hp hx'
      have hd' : (p.1 : ℂ) - (x : ℂ) * (p.2 : ℂ) ≠ 0 := by
        simpa only [mul_comm] using hd
      dsimp only [g, phaseQuotient]
      push_cast
      field_simp [hx0, hd, hd']
    _ = -ibpIntegral w R p (n + 1) := hparts

theorem ibpIntegral_norm_recurrence {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5)
    {p : ℝ × ℝ} (hp : p ∈ offBandParameters) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    R * ‖ibpIntegral w R p n‖ = ‖ibpIntegral w R p (n+1)‖ := by
  have hh := congrArg norm (ibpIntegral_recurrence hw hws hp R n)
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
    Complex.norm_I, mul_one, norm_neg] using hh

/-- Arbitrary-order uniform decay on the fixed compact parameter set. -/
theorem uniform_normalized_decay {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ offBandParameters, ∀ R : ℝ, 0 < R →
      ‖ibpIntegral w R p 0‖ ≤ C / R ^ A := by
  obtain ⟨C, hC, hbound⟩ := ibpAmplitude_uniform_bound hw A
  refine ⟨6 * C, by positivity, ?_⟩
  intro p hp R hR
  have hpower (n : ℕ) : R ^ n * ‖ibpIntegral w R p 0‖ = ‖ibpIntegral w R p n‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        R ^ (n + 1) * ‖ibpIntegral w R p 0‖ = R * (R ^ n * ‖ibpIntegral w R p 0‖) := by ring
        _ = R * ‖ibpIntegral w R p n‖ := by rw [ih]
        _ = ‖ibpIntegral w R p (n + 1)‖ := ibpIntegral_norm_recurrence hw hws hp hR n
  have hnorm : ‖ibpIntegral w R p A‖ ≤ C * |6 - (1 / 3 : ℝ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le (by norm_num : (1 / 3 : ℝ) ≤ 6)] at hx
    rw [norm_mul, norm_logOscillation, mul_one]
    exact hbound p hp x ⟨hx.1.le, hx.2⟩
  apply (le_div_iff₀ (pow_pos hR A)).2
  rw [mul_comm, hpower]
  norm_num at hnorm
  nlinarith

/-- The off-band estimate with the constant chosen before H, v, and k. -/
theorem uniform_offBand_decay {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H v k : ℝ, 0 < H → H ≤ v → v ≤ 2 * H →
      (k < H / (20 * Real.pi) ∨ 4 * H / Real.pi < k) →
      ‖∫ x in (1 / 3 : ℝ)..6, w x *
        Complex.exp (((v * Real.log x - 2 * Real.pi * k * x : ℝ) : ℂ) * Complex.I)‖ ≤
          C / (H + |k|) ^ A := by
  obtain ⟨C, hC, hbound⟩ := uniform_normalized_decay hw hws A
  refine ⟨C, hC, ?_⟩
  intro H v k hH hv hv2 hk
  have hR : 0 < H + |k| := by positivity
  have hh := hbound _ (normalized_offBand_mem hH hv hv2 hk) _ hR
  have heq : ibpIntegral w (H + |k|)
      (v / (H + |k|), (2 * Real.pi * k) / (H + |k|)) 0 =
      ∫ x in (1 / 3 : ℝ)..6, w x *
        Complex.exp (((v * Real.log x - 2 * Real.pi * k * x : ℝ) : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [ibpAmplitude, logOscillation]
    congr 3
    congr 1
    field_simp [hR.ne']
  rwa [heq] at hh

end MathCollab.Density
