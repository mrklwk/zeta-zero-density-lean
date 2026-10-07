module
public import GuthMaynard.SecondDerivative

@[expose] public section

open Set

namespace RiemannZeta.GuthMaynard

/-- Second-order mean value theorem for a unit-spaced second difference.
The proof interpolates the three values by a quadratic and applies Rolle's
theorem twice to the error and once to its first derivative. -/
theorem second_order_mean_value
    (F F' F'' : Real -> Real) (x : Real)
    (hF : forall y, y ∈ Set.Icc x (x + 2) -> HasDerivAt F (F' y) y)
    (hF' : forall y, y ∈ Set.Icc x (x + 2) -> HasDerivAt F' (F'' y) y) :
    exists xi, xi ∈ Set.Ioo x (x + 2) ∧
      F'' xi = F (x + 2) - 2 * F (x + 1) + F x := by
  let a := F (x + 1) - F x
  let D := F (x + 2) - 2 * F (x + 1) + F x
  let q : Real -> Real := fun y =>
    F y - F x - a * (y - x) - D / 2 * (y - x) * (y - x - 1)
  let q' : Real -> Real := fun y =>
    F' y - a - D / 2 * ((y - x) + (y - x - 1))
  have hq (y : Real) (hy : y ∈ Set.Icc x (x + 2)) : HasDerivAt q (q' y) y := by
    dsimp only [q, q', a, D]
    convert (((hF y hy).sub_const (F x)).sub
      ((hasDerivAt_id y).sub_const x |>.const_mul a)).sub
      ((((hasDerivAt_id y).sub_const x).mul
        (((hasDerivAt_id y).sub_const x).sub_const 1)).const_mul (D / 2)) using 1
    · funext z
      simp only [Pi.sub_apply, Pi.mul_apply]
      dsimp only [a, D, id_eq]
      ring
    · dsimp only [a, D, id_eq]
      ring
  have hq' (y : Real) (hy : y ∈ Set.Icc x (x + 2)) :
      HasDerivAt q' (F'' y - D) y := by
    dsimp only [q', a]
    convert (((hF' y hy).sub_const a).sub
      ((((hasDerivAt_id y).sub_const x).add
        (((hasDerivAt_id y).sub_const x).sub_const 1)).const_mul (D / 2))) using 1
    · funext z
      simp only [Pi.sub_apply, Pi.add_apply]
      dsimp only [a, id_eq]
    · ring
  have hq0 : q x = 0 := by dsimp only [q]; ring
  have hq1 : q (x + 1) = 0 := by dsimp only [q, a]; ring
  have hq2 : q (x + 2) = 0 := by dsimp only [q, a, D]; ring
  obtain ⟨c₁, hc₁, hc₁zero⟩ := exists_hasDerivAt_eq_zero (by linarith : x < x + 1)
    (fun y hy => (hq y ⟨hy.1, hy.2.trans (by linarith)⟩).continuousAt.continuousWithinAt)
    (hq0.trans hq1.symm)
    (fun y hy => hq y ⟨hy.1.le, hy.2.le.trans (by linarith)⟩)
  obtain ⟨c₂, hc₂, hc₂zero⟩ := exists_hasDerivAt_eq_zero (by linarith : x + 1 < x + 2)
    (fun y hy => (hq y ⟨(by linarith [hy.1]), hy.2⟩).continuousAt.continuousWithinAt)
    (hq1.trans hq2.symm)
    (fun y hy => hq y ⟨(by linarith [hy.1]), hy.2.le⟩)
  have hc12 : c₁ < c₂ := lt_trans hc₁.2 hc₂.1
  obtain ⟨xi, hxi, hxizero⟩ := exists_hasDerivAt_eq_zero hc12
    (fun y hy => (hq' y ⟨(by linarith [hc₁.1, hy.1]),
      (by linarith [hc₂.2, hy.2])⟩).continuousAt.continuousWithinAt)
    (by rw [hc₁zero, hc₂zero])
    (fun y hy => hq' y ⟨(by linarith [hc₁.1, hy.1]),
      (by linarith [hc₂.2, hy.2])⟩)
  refine ⟨xi, ⟨hc₁.1.trans hxi.1, hxi.2.trans hc₂.2⟩, ?_⟩
  dsimp only [D] at hxizero ⊢
  linarith

end RiemannZeta.GuthMaynard
