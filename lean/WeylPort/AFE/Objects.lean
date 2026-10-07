module
/- McColm source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0. -/
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

-- Lean 4.34 elaborator compatibility.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Literal objects for the Dhiman--Kadiri--Quesada-Herrera paper

Positive-integer sums include the unit term. Complex powers use Mathlib's
principal branch. Defining the remainder does not prove an estimate for it.
-/

namespace DhimanKadiriQuesadaHerrera2026

open scoped BigOperators

/-- The paper's positive-integer Dirichlet term, with principal complex power. -/
noncomputable def zetaTerm (s : ℂ) (n : ℕ) : ℂ := (n : ℂ) ^ (-s)

/-- The actual sharp positive-integer sum through a real cutoff. -/
noncomputable def sharpZetaSum (s : ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, zetaTerm s n

/-- The printed Theorem 9 sum, which omits its unit term. -/
noncomputable def printedAFE1Sum (s : ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 1 ⌊x⌋₊, zetaTerm s n

/-- The chi factor in equation (2.16), using the actual gamma function. -/
noncomputable def chi (s : ℂ) : ℂ :=
  (2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1) * Complex.Gamma (1 - s) *
    Complex.sin ((Real.pi : ℂ) * s / 2)

/-- The literal remainder of the two-polynomial approximate functional equation. -/
noncomputable def afeRemainder (s : ℂ) (x y : ℝ) : ℂ :=
  riemannZeta s - sharpZetaSum s x - chi s * sharpZetaSum (1 - s) y

end DhimanKadiriQuesadaHerrera2026
