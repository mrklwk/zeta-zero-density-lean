module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import WeylPort.AFE.PoissonPartI

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-! # The fully shifted general-N corrected Poisson theorem -/

namespace DhimanKadiriQuesadaHerrera2026

open MeasureTheory

/-- The actual integer-frequency phase shift used in the source's reduction. -/
noncomputable def phaseShift (f : ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ := f x - N * x

/-- Source hypotheses with the monotonicity condition at general N. -/
structure PartIRegularityAt (f g : ℝ → ℝ) (a b : ℝ) (N : ℕ) : Prop where
  lt : a < b
  f_differentiable : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x
  f_deriv_continuous : ContinuousOn (deriv f) (Set.Icc a b)
  lower_frequency_lt : (N : ℝ) < deriv f b
  f_deriv_antitone : AntitoneOn (deriv f) (Set.Icc a b)
  g_differentiable : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ g x
  g_deriv_continuous : ContinuousOn (deriv g) (Set.Icc a b)
  g_nonneg : ∀ x ∈ Set.Icc a b, 0 ≤ g x
  g_antitone : AntitoneOn g (Set.Icc a b)
  g_abs_deriv_antitone : AntitoneOn (fun x => |deriv g x|) (Set.Icc a b)
  g_quotient_antitone : AntitoneOn (fun x => |deriv g x| / (1 + deriv f x - N)) (Set.Icc a b)

/-- The phase shift changes the derivative by exactly N. -/
theorem deriv_phaseShift {f : ℝ → ℝ} (N : ℕ) {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    deriv (phaseShift f N) x = deriv f x - N :=
  deriv_frequency_shift hf N

/-- The endpoint condition implies a positive shifted derivative throughout the interval. -/
theorem PartIRegularityAt.deriv_gt {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    (N : ℝ) < deriv f x :=
  h.lower_frequency_lt.trans_le
    (h.f_deriv_antitone hx (Set.right_mem_Icc.mpr h.lt.le) hx.2)

/-- Every accepted analytic hypothesis is transported to the shifted phase explicitly. -/
theorem PartIRegularityAt.shift {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N) : PartIRegularity (phaseShift f N) g a b := by
  have hd (x : ℝ) (hx : x ∈ Set.Icc a b) := deriv_phaseShift N (h.f_differentiable x hx)
  refine ⟨h.lt, ?_, ?_, ?_, ?_, h.g_differentiable, h.g_deriv_continuous,
    h.g_nonneg, h.g_antitone, h.g_abs_deriv_antitone, ?_⟩
  · intro x hx
    exact (h.f_differentiable x hx).sub (differentiableAt_id.const_mul (N : ℝ))
  · exact (h.f_deriv_continuous.sub continuousOn_const).congr (fun x hx => hd x hx)
  · intro x hx
    rw [hd x hx]
    exact sub_pos.mpr (h.deriv_gt hx)
  · intro x hx y hy hxy
    rw [hd x hx, hd y hy]
    exact sub_le_sub_right (h.f_deriv_antitone hx hy hxy) _
  · intro x hx y hy hxy
    dsimp only
    rw [hd x hx, hd y hy]
    simpa only [← add_sub_assoc] using h.g_quotient_antitone hx hy hxy

/-- The source's integer samples are unchanged under the phase shift. -/
theorem weightedWave_phaseShift_int (f g : ℝ → ℝ) (N : ℕ) (n : ℤ) :
    weightedWave (phaseShift f N) g (n : ℝ) = weightedWave f g (n : ℝ) := by
  unfold weightedWave phaseShift
  have he : 2 * (Real.pi : ℂ) * Complex.I * ((f (n : ℝ) - (N : ℝ) * n : ℝ) : ℂ) =
      2 * Real.pi * Complex.I * (f (n : ℝ) : ℂ) -
        (((N : ℤ) * n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- The actual (a,b] sum is preserved at every integer sample, including negative ones. -/
theorem weighted_sum_phaseShift (f g : ℝ → ℝ) (a b : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave (phaseShift f N) g (n : ℝ)) =
      ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ) := by
  apply Finset.sum_congr rfl
  intro n _
  exact weightedWave_phaseShift_int f g N n

/-- The finite Fourier main term reindexes to the exact source range N ≤ ν ≤ floor(f′(a)). -/
theorem poissonMain_phaseShift {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N) :
    poissonMain (phaseShift f N) g a b ⌊deriv (phaseShift f N) a⌋₊ =
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ x in a..b, (g x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ)) := by
  have ha := Set.left_mem_Icc.mpr h.lt.le
  have hN : N ≤ ⌊deriv f a⌋₊ := Nat.le_floor (h.deriv_gt ha).le
  rw [poissonMain_eq_source, deriv_phaseShift N (h.f_differentiable a ha), Nat.floor_sub_natCast]
  apply Finset.sum_bij (fun (n : ℕ) _ => n + N)
  · intro n hn
    simp only [Finset.mem_Icc] at hn ⊢
    omega
  · intro n _ m _ hnm
    omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    refine ⟨n - N, ?_, by omega⟩
    simp only [Finset.mem_Icc]
    omega
  · intro n _
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only
    unfold phaseShift
    congr 2
    push_cast
    ring

/-- The fractional offset δ is invariant under the integer-frequency shift. -/
theorem phaseShift_delta (y : ℝ) (N : ℕ) :
    1 - Int.fract (y - N) = 1 - Int.fract y := by
  rw [Int.fract_sub_natCast]


/-- The fully shifted logarithmic/digamma remainder, with the invariant source δ. -/
noncomputable def partIShiftAnalyticError (f g : ℝ → ℝ) (a : ℝ) (N : ℕ) : ℝ :=
  let y := deriv f a - N
  let M := ⌊deriv f a⌋₊ - N
  (|deriv g a| + 2 * Real.pi * g a * y) / (2 * Real.pi ^ 2 * y) *
    (Real.log (1 + y) + Real.eulerMascheroniConstant + Real.log ((M : ℝ) + 1) -
      (Complex.digamma ((1 - Int.fract (deriv f a) : ℝ) : ℂ)).re -
        1 / (2 * ((M : ℝ) + 1)) - 1 / (2 * (1 + y)))

/-- The complete corrected general-N remainder, including shifted complex endpoints. -/
noncomputable def partIError (f g : ℝ → ℝ) (a b : ℝ) (N : ℕ) : ℝ :=
  partIShiftAnalyticError f g a N +
    (g b * poissonEndpointMajorant b (deriv f a - N) +
      g a * poissonEndpointMajorant a (deriv f a - N)) / (2 * Real.pi) +
        ‖poissonBoundary (phaseShift f N) g a b‖

/-- The shifted natural floor gives exactly the unshifted fractional offset δ. -/
theorem shifted_floor_delta {y : ℝ} {N : ℕ} (hN : (N : ℝ) ≤ y) :
    ((⌊y⌋₊ - N : ℕ) : ℝ) + 1 - (y - N) = 1 - Int.fract y := by
  rw [← Nat.floor_sub_natCast, natCast_floor_eq_intCast_floor (sub_nonneg.mpr hN),
    Int.floor_sub_natCast, Int.cast_sub, Int.cast_natCast]
  unfold Int.fract
  ring

/-- Every analytic term in the N = 0 bound becomes the fully shifted general-N expression. -/
theorem partIAnalyticError_phaseShift_eq {f g : ℝ → ℝ} {a : ℝ} {N : ℕ}
    (hf : DifferentiableAt ℝ f a) (hN : (N : ℝ) < deriv f a) :
    partIAnalyticError (phaseShift f N) g a = partIShiftAnalyticError f g a N := by
  unfold partIAnalyticError partICoefficient partIShiftAnalyticError
  rw [deriv_phaseShift N hf]
  dsimp only
  rw [Nat.floor_sub_natCast, shifted_floor_delta hN.le]
  rw [div_div]

/-- The complete N = 0 bound transports with all endpoint terms, not only its leading term. -/
theorem partIZeroError_phaseShift_eq {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hf : DifferentiableAt ℝ f a) (hN : (N : ℝ) < deriv f a) :
    partIZeroError (phaseShift f N) g a b = partIError f g a b N := by
  unfold partIZeroError partIError
  rw [partIAnalyticError_phaseShift_eq hf hN, deriv_phaseShift N hf]

/-- The full corrected weighted Part I theorem, for every allowed N and every real endpoint. -/
theorem corrected_poisson_partI {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ x in a..b, (g x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      partIError f g a b N := by
  have he := corrected_poisson_partI_zero h.shift
  have ha := Set.left_mem_Icc.mpr h.lt.le
  rw [weighted_sum_phaseShift, poissonMain_phaseShift h,
    partIZeroError_phaseShift_eq (h.f_differentiable a ha) (h.deriv_gt ha)] at he
  exact he

/-- The fully shifted general-N theorem keeps the printed log(2) half-integer refinement. -/
theorem corrected_poisson_partI_half_integer {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N)
    (ha : ∃ k : ℤ, a = (k : ℝ) + 1 / 2) (hb : ∃ k : ℤ, b = (k : ℝ) + 1 / 2) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ x in a..b, (g x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      partIShiftAnalyticError f g a N +
        (g a + g b) / (2 * Real.pi) * (Real.log 2 + 1 / (deriv f a - N)) := by
  have he := corrected_poisson_partI_zero_half_integer h.shift ha hb
  have ha' := Set.left_mem_Icc.mpr h.lt.le
  rw [weighted_sum_phaseShift, poissonMain_phaseShift h,
    partIAnalyticError_phaseShift_eq (h.f_differentiable a ha') (h.deriv_gt ha'),
      deriv_phaseShift N (h.f_differentiable a ha')] at he
  exact he

/-- The general-N noninteger-endpoint specialization uses the unchanged tilde-S₁ function. -/
theorem corrected_poisson_partI_noninteger {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (h : PartIRegularityAt f g a b N)
    (ha : ∀ k : ℤ, a ≠ (k : ℝ)) (hb : ∀ k : ℤ, b ≠ (k : ℝ)) :
    ‖(∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, weightedWave f g (n : ℝ)) -
      ∑ ν ∈ Finset.Icc N ⌊deriv f a⌋₊,
        ∫ x in a..b, (g x : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * ((f x - (ν : ℝ) * x : ℝ) : ℂ))‖ ≤
      partIShiftAnalyticError f g a N +
        (g b * tildeS1 b (deriv f a - N) + g a * tildeS1 a (deriv f a - N)) / (2 * Real.pi) +
          ‖poissonBoundary (phaseShift f N) g a b‖ := by
  have he := corrected_poisson_partI h
  simpa only [partIError, poissonEndpointMajorant_eq_tildeS1 ha,
    poissonEndpointMajorant_eq_tildeS1 hb] using he


/-- The integer-floor index set is precisely the source's strict-left, closed-right interval. -/
theorem mem_source_sample_interval (a b : ℝ) (n : ℤ) :
    n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋ ↔ a < (n : ℝ) ∧ (n : ℝ) ≤ b := by
  rw [Finset.mem_Ioc, Int.floor_lt, Int.le_floor]

/-- The printed strict phase monotonicity and positive weight imply the accepted regularity interface. -/
theorem partIRegularityAt_of_source_hypotheses {f g : ℝ → ℝ} {a b : ℝ} {N : ℕ}
    (hab : a < b) (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x)
    (hfc : ContinuousOn (deriv f) (Set.Icc a b)) (hN : (N : ℝ) < deriv f b)
    (hfa : StrictAntiOn (deriv f) (Set.Icc a b))
    (hgd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ g x)
    (hgdc : ContinuousOn (deriv g) (Set.Icc a b))
    (hgp : ∀ x ∈ Set.Icc a b, 0 < g x) (hga : AntitoneOn g (Set.Icc a b))
    (hgda : AntitoneOn (fun x => |deriv g x|) (Set.Icc a b))
    (hgdq : AntitoneOn (fun x => |deriv g x| / (1 + deriv f x - N)) (Set.Icc a b)) :
    PartIRegularityAt f g a b N :=
  ⟨hab, hfd, hfc, hN, hfa.antitoneOn, hgd, hgdc, fun x hx => (hgp x hx).le, hga, hgda, hgdq⟩

end DhimanKadiriQuesadaHerrera2026
