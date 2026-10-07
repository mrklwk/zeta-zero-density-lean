module
public import Init

@[expose] public section

/- Infrastructure smoke test only.
   No statement of the analytic reflection lemma is encoded here. -/
namespace MathCollab

theorem add_zero_smoke (n : Nat) : n + 0 = n := by
  rfl

theorem identity_smoke (P : Prop) (h : P) : P := by
  exact h

#print axioms add_zero_smoke
#print axioms identity_smoke

end MathCollab
