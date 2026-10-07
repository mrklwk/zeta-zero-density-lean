module
/-
Pole-removal and finite contour argument adapted from McColm TypeIICoverage,
exact pin 2ace9e7c09a69fdcd1edae1ab6deb7cb3b4df1be, MIT.
X, Y and rectangle height R are independent parameters. The actual zeta
function and the existing floor-cutoff mollifier are retained.
-/
public import MathCollab.Density.DetectorMellin
public import MathCollab.Density.AbelZetaGrowth
public import MathCollab.Density.DetectorGamma
public import MathCollab.Density.RectangleResidue

@[expose] public section

open Complex MeasureTheory Set Filter
open MathCollab.Density.ZetaGrowth MathCollab.Density.Contour
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density

def shiftedRegularizedZeta (ρ s : ℂ) : ℂ :=
  regularizedRiemannZeta (ρ + s)

/-- The analytic quotient which removes the apparent `Γ(s)` singularity at
`s = 0` when `ζ(ρ)=0`. -/
def zetaZeroQuotient (ρ s : ℂ) : ℂ :=
  dslope (shiftedRegularizedZeta ρ) 0 s

/-- Entire numerator on the detector rectangle.  The only remaining pole
of the original contour integrand is represented explicitly by division by
`s - (1 - ρ)`. -/
def detectorContourNumerator (ρ : ℂ) (X Y : ℝ) (s : ℂ) : ℂ :=
  (Y : ℂ) ^ s * Complex.Gamma (s + 1) *
    zetaMollifier X (ρ + s) * zetaZeroQuotient ρ s

/-- The residue crossed at the zeta pole `s = 1 - ρ`. -/
def detectorResidue (ρ : ℂ) (X Y : ℝ) : ℂ :=
  (Y : ℂ) ^ (1 - ρ) * Complex.Gamma (1 - ρ) *
    zetaMollifier X 1

theorem shiftedRegularizedZeta_zero {ρ : ℂ}
    (hρOne : ρ ≠ 1) (hZero : riemannZeta ρ = 0) :
    shiftedRegularizedZeta ρ 0 = 0 := by
  rw [shiftedRegularizedZeta, add_zero, regularizedRiemannZeta,
    Function.update_of_ne hρOne, hZero, mul_zero]

theorem shiftedRegularizedZeta_eq {ρ s : ℂ}
    (hPole : ρ + s ≠ 1) :
    shiftedRegularizedZeta ρ s =
      (s - (1 - ρ)) * riemannZeta (ρ + s) := by
  rw [shiftedRegularizedZeta, regularizedRiemannZeta,
    Function.update_of_ne hPole]
  ring

/-- Away from the two removed points, the analytic numerator divided by its
explicit zeta-pole factor is exactly the original detector integrand. -/
theorem detectorContourNumerator_div_eq_integrand {ρ s : ℂ} {X Y : ℝ}
    (hρOne : ρ ≠ 1) (hZero : riemannZeta ρ = 0)
    (hsZero : s ≠ 0) (hsPole : s ≠ 1 - ρ) :
    detectorContourNumerator ρ X Y s / (s - (1 - ρ)) =
      (Y : ℂ) ^ s * Complex.Gamma s *
        zetaMollifier X (ρ + s) * riemannZeta (ρ + s) := by
  have hR0 := shiftedRegularizedZeta_zero hρOne hZero
  have hShiftPole : ρ + s ≠ 1 := by
    intro h
    apply hsPole
    linear_combination h
  have hSlope := sub_smul_dslope_of_zero hR0 s
  have hQuotient : s * zetaZeroQuotient ρ s =
      (s - (1 - ρ)) * riemannZeta (ρ + s) := by
    simpa [zetaZeroQuotient, shiftedRegularizedZeta_eq hShiftPole,
      smul_eq_mul] using hSlope
  rw [div_eq_iff (sub_ne_zero.mpr hsPole)]
  unfold detectorContourNumerator
  rw [Complex.Gamma_add_one s hsZero]
  calc
    (Y : ℂ) ^ s * (s * Complex.Gamma s) *
          zetaMollifier X (ρ + s) * zetaZeroQuotient ρ s =
        (Y : ℂ) ^ s * Complex.Gamma s *
          zetaMollifier X (ρ + s) *
            (s * zetaZeroQuotient ρ s) := by ring
    _ = (Y : ℂ) ^ s * Complex.Gamma s *
          zetaMollifier X (ρ + s) *
            ((s - (1 - ρ)) * riemannZeta (ρ + s)) := by rw [hQuotient]
    _ = ((Y : ℂ) ^ s * Complex.Gamma s *
          zetaMollifier X (ρ + s) * riemannZeta (ρ + s)) *
            (s - (1 - ρ)) := by ring

/-- Exact residue evaluation at `s = 1 - ρ`. -/
theorem detectorContourNumerator_at_pole {ρ : ℂ} {X Y : ℝ}
    (hρOne : ρ ≠ 1) (hZero : riemannZeta ρ = 0) :
    detectorContourNumerator ρ X Y (1 - ρ) = detectorResidue ρ X Y := by
  let p : ℂ := 1 - ρ
  have hpZero : p ≠ 0 := sub_ne_zero.mpr hρOne.symm
  have hR0 := shiftedRegularizedZeta_zero hρOne hZero
  have hRp : shiftedRegularizedZeta ρ p = 1 := by
    have hρp : ρ + p = 1 := by dsimp [p]; ring
    rw [shiftedRegularizedZeta, hρp, regularizedRiemannZeta]
    simp
  have hSlope := sub_smul_dslope_of_zero hR0 p
  have hQuotient : p * zetaZeroQuotient ρ p = 1 := by
    simpa [zetaZeroQuotient, hRp, smul_eq_mul] using hSlope
  unfold detectorContourNumerator detectorResidue
  change (Y : ℂ) ^ p * Complex.Gamma (p + 1) *
      zetaMollifier X (ρ + p) * zetaZeroQuotient ρ p =
    (Y : ℂ) ^ p * Complex.Gamma p * zetaMollifier X 1
  rw [Complex.Gamma_add_one p hpZero]
  have hρp : ρ + p = 1 := by dsimp [p]; ring
  rw [hρp]
  calc
    (Y : ℂ) ^ p * (p * Complex.Gamma p) *
          zetaMollifier X 1 * zetaZeroQuotient ρ p =
        (Y : ℂ) ^ p * Complex.Gamma p *
          zetaMollifier X 1 * (p * zetaZeroQuotient ρ p) := by ring
    _ = (Y : ℂ) ^ p * Complex.Gamma p * zetaMollifier X 1 := by
      rw [hQuotient, mul_one]

theorem differentiableAt_shiftedRegularizedZeta (ρ s : ℂ) :
    DifferentiableAt ℂ (shiftedRegularizedZeta ρ) s := by
  unfold shiftedRegularizedZeta
  exact (differentiableAt_regularizedRiemannZeta (ρ + s)).comp s
    ((differentiableAt_const (𝕜 := ℂ) ρ).add differentiableAt_id)

theorem differentiableAt_zetaZeroQuotient (ρ s : ℂ) :
    DifferentiableAt ℂ (zetaZeroQuotient ρ) s := by
  have hShift : DifferentiableOn ℂ (shiftedRegularizedZeta ρ) Set.univ :=
    fun z _hz => (differentiableAt_shiftedRegularizedZeta ρ z).differentiableWithinAt
  have hSlope : DifferentiableOn ℂ
      (dslope (shiftedRegularizedZeta ρ) 0) Set.univ :=
    (Complex.differentiableOn_dslope
      (Filter.univ_mem : Set.univ ∈ nhds (0 : ℂ))).2 hShift
  exact differentiableWithinAt_univ.mp (hSlope s (Set.mem_univ s))

/-- The pole-removed numerator is holomorphic throughout the open half-plane
`Re s > -1`, which contains every rectangle used to shift from `1/2` to
`1/2 - Re ρ` in the zero-density range. -/
theorem differentiableOn_detectorContourNumerator {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) :
    DifferentiableOn ℂ (detectorContourNumerator ρ X Y)
      {s : ℂ | -(1 : ℝ) < s.re} := by
  intro s hs
  change -(1 : ℝ) < s.re at hs
  have hBase : (Y : ℂ) ≠ 0 := by exact_mod_cast hY.ne'
  have hPow : DifferentiableAt ℂ (fun z : ℂ => (Y : ℂ) ^ z) s :=
    differentiableAt_id.const_cpow (Or.inl hBase)
  have hGammaNoPole : ∀ m : ℕ, s + 1 ≠ -m := by
    intro m hm
    have hRe := congrArg Complex.re hm
    have hmNonneg : (0 : ℝ) ≤ m := by positivity
    simp at hRe
    linarith
  have hGamma : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) s :=
    (Complex.differentiableAt_Gamma (s + 1) hGammaNoPole).comp s
      (differentiableAt_id.add_const 1)
  have hMollifier : DifferentiableAt ℂ
      (fun z : ℂ => zetaMollifier X (ρ + z)) s :=
    (differentiableAt_zetaMollifier X (ρ + s)).comp s
      ((differentiableAt_const (𝕜 := ℂ) ρ).add differentiableAt_id)
  have hQuotient := differentiableAt_zetaZeroQuotient ρ s
  exact (((hPow.mul hGamma).mul hMollifier).mul hQuotient).differentiableWithinAt

set_option maxHeartbeats 800000 in
/-- Finite-height rectangle shift.  The apparent pole at zero has already
been removed, so the rectangle crosses exactly the zeta pole `1 - ρ`. -/
theorem detector_finite_rectangle_residue {ρ : ℂ} {X Y R : ℝ}
    (hY : 0 < Y) (hβLower : 3/4 ≤ ρ.re) (hβUpper : ρ.re < 1)
    (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral'
      (fun s => detectorContourNumerator ρ X Y s / (s - (1 - ρ)))
      ((a : ℂ) - (R : ℂ)*I) (((1/2 : ℝ) : ℂ) + (R : ℂ)*I) =
        detectorResidue ρ X Y := by
  let a : ℝ := 1/2 - ρ.re
  let z : ℂ := (a : ℂ) - (R : ℂ) * I
  let w : ℂ := ((1 / 2 : ℝ) : ℂ) + (R : ℂ) * I
  let p : ℂ := 1 - ρ
  let N : ℂ → ℂ := detectorContourNumerator ρ X Y
  let f : ℂ → ℂ := fun s => N s / (s - p)
  let g : ℂ → ℂ := dslope N p
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg _) hR
  have hγLower := (abs_lt.mp hR).1
  have hγUpper := (abs_lt.mp hR).2
  have hρOne : ρ ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    linarith
  have hzRe : z.re ≤ w.re := by simp [z, w, a]; linarith
  have hzIm : z.im ≤ w.im := by simp [z, w]; linarith
  have hpInterior : Rectangle z w ∈ nhds p := by
    rw [rectangle_mem_nhds_iff, Set.uIoo_of_le hzRe, Set.uIoo_of_le hzIm,
      mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
    constructor
    · simp [p, z, w, a]
      constructor <;> linarith
    · simp [p, z, w]
      constructor <;> linarith
  have hRectSubset : Rectangle z w ⊆ {s : ℂ | -(1 : ℝ) < s.re} := by
    intro s hs
    have hsBounds := (mem_Rect hzRe hzIm s).mp hs
    change -(1 : ℝ) < s.re
    have haLower : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
    have hzReal : z.re = a := by simp [z]
    linarith [hsBounds.1]
  have hNdiff : DifferentiableOn ℂ N (Rectangle z w) := by
    exact (differentiableOn_detectorContourNumerator hY).mono hRectSubset
  have hgHolo : HolomorphicOn g (Rectangle z w) := by
    exact (Complex.differentiableOn_dslope hpInterior).2 hNdiff
  have hNp : N p = detectorResidue ρ X Y := by
    simpa [N, p] using detectorContourNumerator_at_pole
      (X := X) (Y := Y) hρOne hZero
  have hPrincipal : Set.EqOn
      (f - fun s => detectorResidue ρ X Y / (s - p)) g
      (Rectangle z w \ {p}) := by
    intro s hs
    have hsp : s ≠ p := by simpa using hs.2
    have hSlope := sub_smul_dslope N p s
    change f s - detectorResidue ρ X Y / (s - p) = g s
    rw [← hNp]
    dsimp [f, g]
    rw [← sub_div]
    rw [← hSlope]
    rw [smul_eq_mul, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hsp)]
  have hResidue := ResidueTheoremOnRectangleWithSimplePole
    hzRe hzIm hpInterior hgHolo hPrincipal
  simpa [a, z, w, p, N, f, g] using hResidue


/-- Exact finite shift for the literal kernel; both exceptional points are
strictly interior for every independently chosen R>|Im(rho)|. -/
theorem detector_finite_rectangle_kernel {ρ : ℂ} {X Y R : ℝ}
    (hY : 0 < Y) (hβLower : 3/4 ≤ ρ.re) (hβUpper : ρ.re < 1)
    (hR : |ρ.im| < R) (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1/2 - ρ.re
    RectangleIntegral' (detectorKernel ρ X Y)
      ((a : ℂ)-(R : ℂ)*I) (((1/2 : ℝ) : ℂ)+(R : ℂ)*I) =
        detectorResidue ρ X Y := by
  let a : ℝ := 1 / 2 - ρ.re
  let z : ℂ := (a : ℂ) - (R : ℂ) * I
  let w : ℂ := ((1 / 2 : ℝ) : ℂ) + (R : ℂ) * I
  have hρOne : ρ ≠ 1 := by
    intro h
    have hRe := congrArg Complex.re h
    simp at hRe
    linarith
  have hRpos : 0 < R := lt_of_le_of_lt (abs_nonneg _) hR
  have hγLower := (abs_lt.mp hR).1
  have hγUpper := (abs_lt.mp hR).2
  have hFinite := detector_finite_rectangle_residue (X := X) hY hβLower hβUpper hR hZero
  change RectangleIntegral' (detectorKernel ρ X Y) z w =
    detectorResidue ρ X Y
  rw [← hFinite]
  apply RectangleIntegral'_congr
  intro s hs
  have hsZero : s ≠ 0 := by
    intro hs0
    rw [hs0] at hs
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm,
      Set.mem_singleton_iff] at hs
    rcases hs with ((hBottom | hLeft) | hTop) | hRight
    · have : (0 : ℝ) = -R := by simpa [z, w] using hBottom.2
      linarith
    · have : (0 : ℝ) = a := by simpa [z, w] using hLeft.1
      dsimp [a] at this
      linarith
    · have : (0 : ℝ) = R := by simpa [z, w] using hTop.2
      linarith
    · have : (0 : ℝ) = 1 / 2 := by simpa [z, w] using hRight.1
      norm_num at this
  have hsPole : s ≠ 1 - ρ := by
    intro hsp
    rw [hsp] at hs
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm,
      Set.mem_singleton_iff] at hs
    rcases hs with ((hBottom | hLeft) | hTop) | hRight
    · have : -ρ.im = -R := by simpa [z, w] using hBottom.2
      linarith
    · have : 1 - ρ.re = a := by simpa [z, w] using hLeft.1
      dsimp [a] at this
      linarith
    · have : -ρ.im = R := by simpa [z, w] using hTop.2
      linarith
    · have : 1 - ρ.re = 1 / 2 := by simpa [z, w] using hRight.1
      linarith
  exact (detectorContourNumerator_div_eq_integrand hρOne hZero hsZero hsPole).symm


end MathCollab.Density
