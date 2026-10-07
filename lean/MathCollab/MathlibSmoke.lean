module
public import Mathlib.Basic.Real.Basic

@[expose] public section

/- Standard real arithmetic to check the pinned mathlib dependency.
   This does not express or prove the analytic reflection lemma. -/
namespace MathCollab

theorem real_add_zero_smoke (x : ℝ) : x + 0 = x := by
  exact add_zero x

theorem square_nonnegative_smoke (x : ℝ) : 0 ≤ x * x := by
  exact mul_self_nonneg x

#print axioms real_add_zero_smoke
#print axioms square_nonnegative_smoke

end MathCollab
