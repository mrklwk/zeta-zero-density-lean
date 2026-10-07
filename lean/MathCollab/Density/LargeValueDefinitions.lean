module
public import MathCollab.Density.Reflection
public import Mathlib.NumberTheory.Divisors

@[expose] public section

open Real Complex Set
open scoped BigOperators ContDiff

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- The source polynomial has support (N,2N], distinct from the auxiliary [M,2M). -/
def detectingPolynomial (N : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc N (2*N), a n * dirichletPhase ((n : ℝ)/N) t

def kernelEnergy (w : ReflectionCutoff) (L : ℝ) (U : Finset ℝ) : ℝ :=
  ∑ t ∈ U, ∑ u ∈ U, ‖hKernel w L (t-u)‖ ^ 2

def oneSeparated (U : Finset ℝ) : Prop :=
  ∀ t ∈ U, ∀ u ∈ U, t ≠ u → 1 ≤ |t-u|

def intervalSpan (U : Finset ℝ) : ℝ :=
  if h : U.Nonempty then U.max' h - U.min' h else 0

def localDiameter (U : Finset ℝ) : ℝ := 1 + intervalSpan U

def divisorMaximum (T : ℝ) : ℕ :=
  (Finset.Icc 1 ⌈32*(T+1)⌉₊).sup (fun m => m.divisors.card)

def bootstrapScalar (T : ℝ) (N : ℕ) (V : ℝ) : ℝ :=
  (N : ℝ) * divisorMaximum T / V^2

/-- Only the packet's original large-value hypotheses; no analytic conclusion is a field. -/
structure LargeValueData (κ : ℝ) where
  T : ℝ
  N : ℕ
  V : ℝ
  a : ℕ → ℂ
  W : Finset ℝ
  t₀ : ℝ
  T_ge_two : 2 ≤ T
  N_pos : 0 < N
  V_pos : 0 < V
  scale_lower : T ^ (1/3 : ℝ) ≤ (N : ℝ)
  scale_upper : (N : ℝ) ≤ T
  height : (N : ℝ) ^ (3/4+κ) ≤ V
  coefficients : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ 1
  location : ∀ t ∈ W, t₀ ≤ t ∧ t ≤ t₀+T
  separated : oneSeparated W
  large : ∀ t ∈ W, V ≤ ‖detectingPolynomial N a t‖

theorem detectingPolynomial_norm_le {N : ℕ} {a : ℕ → ℂ}
    (ha : ∀ n ∈ Finset.Ioc N (2*N), ‖a n‖ ≤ 1) (t : ℝ) :
    ‖detectingPolynomial N a t‖ ≤ N := by
  calc
    _ ≤ ∑ n ∈ Finset.Ioc N (2*N), ‖a n * dirichletPhase ((n : ℝ)/N) t‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc N (2*N), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa only [norm_mul, norm_dirichletPhase, mul_one] using ha n hn
    _ = _ := by simp; omega

theorem LargeValueData.height_le_length {κ : ℝ} (d : LargeValueData κ) (hW : d.W.Nonempty) :
    d.V ≤ d.N := by
  obtain ⟨t, ht⟩ := hW
  exact (d.large t ht).trans (detectingPolynomial_norm_le d.coefficients t)

theorem kernelEnergy_nonneg (w : ReflectionCutoff) (L : ℝ) (U : Finset ℝ) :
    0 ≤ kernelEnergy w L U :=
  Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

theorem oneSeparated_subset {U W : Finset ℝ} (hW : oneSeparated W) (hU : U ⊆ W) : oneSeparated U :=
  fun t ht u hu hne => hW t (hU ht) u (hU hu) hne

end MathCollab.Density
