module
public import MathCollab.Density.UniformIBP
public import Mathlib.Analysis.PSeries

@[expose] public section

open Real Complex Set MeasureTheory
open scoped BigOperators ContDiff

noncomputable section
namespace MathCollab.Density

/-- The manuscript's explicit Dirichlet phase, using the real logarithm. -/
def dirichletPhase (x v : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((v * Real.log x : ℝ) : ℂ))

/-- Reflection only needs the real smooth cutoff and its support condition. -/
structure ReflectionCutoff where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ ∞ toFun
  support : tsupport toFun ⊆ Icc (1 / 2 : ℝ) 5

instance : CoeFun ReflectionCutoff (fun _ => ℝ → ℝ) := ⟨ReflectionCutoff.toFun⟩

/-- The nonzero Poisson-mode integral in the exact source convention. -/
def modeIntegral (w : ℝ → ℂ) (v k : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), w x *
    Complex.exp (((v * Real.log x - 2 * Real.pi * k * x : ℝ) : ℂ) * Complex.I)

def cutoffIntegral (w : ReflectionCutoff) (v : ℝ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (w x : ℂ) * dirichletPhase x v

/-- The n=0 summand vanishes by the support condition; all nonzero terms are finite. -/
def hKernel (w : ReflectionCutoff) (L v : ℝ) : ℂ :=
  (∑' n : ℕ, (w ((n : ℝ) / L) : ℂ) * dirichletPhase ((n : ℝ) / L) v) -
    (L : ℂ) * cutoffIntegral w v

def dyadicPolynomial (M : ℕ) (v : ℝ) : ℂ :=
  ∑ q ∈ Finset.Ico M (2 * M), dirichletPhase ((q : ℝ) / M) v

def completePairEnergy (M : ℕ) (U : Finset ℝ) : ℝ :=
  ∑ t ∈ U, ∑ u ∈ U, ‖dyadicPolynomial M (t - u)‖ ^ 2

def shellEnergy (w : ReflectionCutoff) (L H : ℝ) (U : Finset ℝ) : ℝ :=
  ∑ t ∈ U, ∑ u ∈ U, if H ≤ |t-u| ∧ |t-u| < 2*H then ‖hKernel w L (t-u)‖ ^ 2 else 0

/-- The exact fixed band, without a scale-dependent enlargement. -/
def inReflectionBand (L H : ℝ) (m : ℤ) : Prop :=
  0 < m ∧ H / (20 * Real.pi * L) ≤ (m : ℝ) ∧ (m : ℝ) ≤ 4 * H / (Real.pi * L)

instance (L H : ℝ) (m : ℤ) : Decidable (inReflectionBand L H m) := Classical.propDecidable _

def localSet (U : Finset ℝ) (H : ℝ) (j : ℤ) : Finset ℝ :=
  U.filter (fun t => (j : ℝ) * H ≤ t ∧ t < ((j : ℝ) + 3) * H)

def discardedMode (w : ℝ → ℂ) (L H v : ℝ) (m : ℤ) : ℂ :=
  if m ≠ 0 ∧ ¬inReflectionBand L H m then modeIntegral w v ((m : ℝ) * L) else 0

theorem modeIntegral_eq_interval {w : ℝ → ℂ}
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) (v k : ℝ) :
    modeIntegral w v k = ∫ x in (1 / 3 : ℝ)..6, w x *
      Complex.exp (((v * Real.log x - 2 * Real.pi * k * x : ℝ) : ℂ) * Complex.I) := by
  let f : ℝ → ℂ := fun x => w x *
    Complex.exp (((v * Real.log x - 2 * Real.pi * k * x : ℝ) : ℂ) * Complex.I)
  have hs : Function.support f ⊆ Icc (1 / 2 : ℝ) 5 := by
    intro x hx
    apply hws
    apply subset_tsupport w
    intro hwx
    exact hx (by simp [f, hwx])
  have hi : Function.support f ⊆ Ioc (1 / 3 : ℝ) 6 := by
    intro x hx
    have hh := hs hx
    constructor <;> linarith [hh.1, hh.2]
  rw [intervalIntegral.integral_eq_integral_of_support_subset hi]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  by_contra hf
  have hpos := (hs hf).1
  apply hx
  change 0 < x
  linarith

theorem uniform_offBand_modeIntegral {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ H v k : ℝ, 0 < H → H ≤ v → v ≤ 2 * H →
      (k < H / (20 * Real.pi) ∨ 4 * H / Real.pi < k) →
      ‖modeIntegral w v k‖ ≤ C / (H + |k|) ^ A := by
  obtain ⟨C, hC, hh⟩ := uniform_offBand_decay hw hws A
  refine ⟨C, hC, ?_⟩
  intro H v k hH hv hv2 hk
  rw [modeIntegral_eq_interval hws]
  exact hh H v k hH hv hv2 hk

theorem outsideBand_scaled {L H : ℝ} (hL : 0 < L) (hH : 0 < H)
    {m : ℤ} (hm : m ≠ 0) (hout : ¬inReflectionBand L H m) :
    (m : ℝ) * L < H / (20 * Real.pi) ∨ 4 * H / Real.pi < (m : ℝ) * L := by
  by_cases hmpos : 0 < m
  · by_cases hlo : H / (20 * Real.pi * L) ≤ (m : ℝ)
    · have hhi : 4 * H / (Real.pi * L) < (m : ℝ) := by
        by_contra hn
        exact hout ⟨hmpos, hlo, le_of_not_gt hn⟩
      right
      apply (div_lt_iff₀ Real.pi_pos).2
      have hh := (div_lt_iff₀ (mul_pos Real.pi_pos hL)).1 hhi
      nlinarith
    · left
      have hh := (lt_div_iff₀ (mul_pos (by positivity) hL)).1 (lt_of_not_ge hlo)
      apply (lt_div_iff₀ (by positivity)).2
      nlinarith
  · left
    have hmneg : (m : ℝ) < 0 := by exact_mod_cast (lt_of_le_of_ne (le_of_not_gt hmpos) hm)
    exact (mul_neg_of_neg_of_pos hmneg hL).trans (by positivity)

def integerPowerMajorant (A : ℕ) (m : ℤ) : ℝ := 1 / |(m : ℝ)| ^ A

theorem summable_integerPowerMajorant {A : ℕ} (hA : 1 < A) :
    Summable (integerPowerMajorant A) := by
  unfold integerPowerMajorant
  have hh := (summable_one_div_int_pow.mpr hA).norm
  simpa only [integerPowerMajorant, Real.norm_eq_abs, abs_div, abs_one, abs_pow] using hh

theorem uniform_discarded_modes {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) {A : ℕ} (hA : 1 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L H v : ℝ, 0 < L → 0 < H → H ≤ v → v ≤ 2 * H →
      Summable (fun m : ℤ => ‖discardedMode w L H v m‖) ∧
      ‖(L : ℂ) * ∑' m : ℤ, discardedMode w L H v m‖ ≤ K * L / L ^ A := by
  obtain ⟨C, hC, hbound⟩ := uniform_offBand_modeIntegral hw hws A
  let Z := ∑' m : ℤ, integerPowerMajorant A m
  have hZ : 0 ≤ Z := tsum_nonneg (fun m => by unfold integerPowerMajorant; positivity)
  refine ⟨C * Z, mul_nonneg hC hZ, ?_⟩
  intro L H v hL hH hv hv2
  have hp : Summable (fun m : ℤ => (C / L ^ A) * integerPowerMajorant A m) :=
    (summable_integerPowerMajorant hA).mul_left (C / L ^ A)
  have hb (m : ℤ) : ‖discardedMode w L H v m‖ ≤ (C / L ^ A) * integerPowerMajorant A m := by
    unfold discardedMode
    split_ifs with hm
    · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.1
      have habs : 0 < |(m : ℝ)| := abs_pos.mpr hmR
      calc
        ‖modeIntegral w v ((m : ℝ) * L)‖ ≤ C / (H + |(m : ℝ) * L|) ^ A :=
          hbound H v _ hH hv hv2 (outsideBand_scaled hL hH hm.1 hm.2)
        _ ≤ C / (|(m : ℝ)| * L) ^ A := by
          rw [abs_mul, abs_of_pos hL]
          apply div_le_div_of_nonneg_left hC (pow_pos (mul_pos habs hL) A)
          exact pow_le_pow_left₀ (by positivity) (by linarith) A
        _ = (C / L ^ A) * integerPowerMajorant A m := by
          unfold integerPowerMajorant
          rw [mul_pow]
          field_simp
    · simp only [norm_zero]
      unfold integerPowerMajorant
      positivity
  have hsumNorm : Summable (fun m : ℤ => ‖discardedMode w L H v m‖) :=
    hp.of_nonneg_of_le (fun m => norm_nonneg _) hb
  refine ⟨hsumNorm, ?_⟩
  have hsum := tsum_of_norm_bounded hp.hasSum hb
  rw [tsum_mul_left] at hsum
  calc
    ‖(L : ℂ) * ∑' m : ℤ, discardedMode w L H v m‖ =
        L * ‖∑' m : ℤ, discardedMode w L H v m‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    _ ≤ L * ((C / L ^ A) * Z) := mul_le_mul_of_nonneg_left hsum hL.le
    _ = (C * Z) * L / L ^ A := by ring

theorem zero_normalized_mem {k : ℝ} (hk : k ≠ 0) :
    (0, 2 * Real.pi * k / |k|) ∈ offBandParameters := by
  have ha : 0 < |k| := abs_pos.mpr hk
  have he : abs (2 * Real.pi * k / |k|) = 2 * Real.pi := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi), abs_abs]
    field_simp
  refine ⟨by norm_num, he.le, ?_⟩
  intro x hx
  change (1 / 300 : ℝ) ≤ |0 - 2 * Real.pi * k / |k| * x|
  rw [zero_sub, abs_neg, abs_mul, he, abs_of_pos (by linarith [hx.1] : 0 < x)]
  nlinarith [Real.pi_gt_three, hx.1]

theorem uniform_zero_modeIntegral {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) (A : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℝ, k ≠ 0 → ‖modeIntegral w 0 k‖ ≤ C / |k| ^ A := by
  obtain ⟨C, hC, hh⟩ := uniform_normalized_decay hw hws A
  refine ⟨C, hC, ?_⟩
  intro k hk
  have ha : 0 < |k| := abs_pos.mpr hk
  have hbound := hh _ (zero_normalized_mem hk) _ ha
  have heq : ibpIntegral w |k| (0, 2 * Real.pi * k / |k|) 0 = modeIntegral w 0 k := by
    rw [modeIntegral_eq_interval hws]
    apply intervalIntegral.integral_congr
    intro x _
    simp only [ibpAmplitude, logOscillation, zero_mul, zero_sub]
    congr 3
    congr 1
    field_simp [ha.ne']
  rwa [heq] at hbound

def nonzeroMode (w : ℝ → ℂ) (L v : ℝ) (m : ℤ) : ℂ :=
  if m = 0 then 0 else modeIntegral w v ((m : ℝ) * L)

/-- The diagonal Poisson-mode sum has the same uniform scale decay. -/
theorem uniform_zero_modes {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 / 2 : ℝ) 5) {A : ℕ} (hA : 1 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ, 0 < L →
      Summable (fun m : ℤ => ‖nonzeroMode w L 0 m‖) ∧
      ‖(L : ℂ) * ∑' m : ℤ, nonzeroMode w L 0 m‖ ≤ K * L / L ^ A := by
  obtain ⟨C, hC, hbound⟩ := uniform_zero_modeIntegral hw hws A
  let Z := ∑' m : ℤ, integerPowerMajorant A m
  have hZ : 0 ≤ Z := tsum_nonneg (fun m => by unfold integerPowerMajorant; positivity)
  refine ⟨C * Z, mul_nonneg hC hZ, ?_⟩
  intro L hL
  have hp : Summable (fun m : ℤ => (C / L ^ A) * integerPowerMajorant A m) :=
    (summable_integerPowerMajorant hA).mul_left (C / L ^ A)
  have hb (m : ℤ) : ‖nonzeroMode w L 0 m‖ ≤ (C / L ^ A) * integerPowerMajorant A m := by
    unfold nonzeroMode
    split_ifs with hm
    · simp only [norm_zero]
      unfold integerPowerMajorant
      positivity
    · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      calc
        ‖modeIntegral w 0 ((m : ℝ) * L)‖ ≤ C / |(m : ℝ) * L| ^ A :=
          hbound _ (mul_ne_zero hmR hL.ne')
        _ = (C / L ^ A) * integerPowerMajorant A m := by
          unfold integerPowerMajorant
          rw [abs_mul, abs_of_pos hL, mul_pow]
          field_simp
  refine ⟨hp.of_nonneg_of_le (fun m => norm_nonneg _) hb, ?_⟩
  have hsum := tsum_of_norm_bounded hp.hasSum hb
  rw [tsum_mul_left] at hsum
  calc
    ‖(L : ℂ) * ∑' m : ℤ, nonzeroMode w L 0 m‖ =
        L * ‖∑' m : ℤ, nonzeroMode w L 0 m‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    _ ≤ L * ((C / L ^ A) * Z) := mul_le_mul_of_nonneg_left hsum hL.le
    _ = (C * Z) * L / L ^ A := by ring

end MathCollab.Density
