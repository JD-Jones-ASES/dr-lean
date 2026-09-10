import DR.Rectangular.FourRowMinorantEqualRows
import DR.Rectangular.FourRowMinorantThreeExtrema

/-!
# Exact stationary algebra on a proper three-coordinate face

The stationary coordinates and value are proved as identities of the
actual homogeneous objective on a three-coordinate face.
The fixed-moment numerator is affine in the three-coordinate product.
No feasibility or sign of an unconstrained stationary vector is asserted.
-/

namespace DittertRybin
open scoped BigOperators

noncomputable def fourRowThreeDenominator (s t d : ℝ) : ℝ := 4*d*(s+d)*(4*t-s^2)

noncomputable def fourRowThreePhi (s t d x : ℝ) : ℝ :=
  (s^2-3*d*s-2*d^2)*x^2+
    (d^2*s+2*d*s^2-2*d*t-s^3+2*s*t)*x+d*(s+d)*(4*t-s^2)

noncomputable def fourRowThreeStationary (a b c d : ℝ) : Fin 4 → ℝ :=
  let s := a+b+c
  let t := a*b+a*c+b*c
  ![fourRowThreePhi s t d a/fourRowThreeDenominator s t d,
    fourRowThreePhi s t d b/fourRowThreeDenominator s t d,
    fourRowThreePhi s t d c/fourRowThreeDenominator s t d,0]

noncomputable def fourRowThreeValueBase (s t d : ℝ) : ℝ :=
  -d^4*s^3+4*d^4*s*t-2*d^3*s^4+13*d^3*s^2*t-20*d^3*t^2-
    d^2*s^5+8*d^2*s^3*t-16*d^2*s*t^2-d*s^4*t+4*d*s^2*t^2

noncomputable def fourRowThreeValueSlope (s t d : ℝ) : ℝ :=
  -d^4-3*d^3*s+2*d^2*s^2-13*d^2*t+7*d*s^3-22*d*s*t-s^4+3*s^2*t

theorem fourRowThreeDenominator_pos {s t d : ℝ} (hd : 0 < d)
    (hsd : 0 < s+d) (hD : 0 < 4*t-s^2) : 0 < fourRowThreeDenominator s t d := by
  unfold fourRowThreeDenominator
  positivity

theorem fourRowThreePhi_mass (a b c d : ℝ) :
    fourRowThreePhi (a+b+c) (a*b+a*c+b*c) d a+
      fourRowThreePhi (a+b+c) (a*b+a*c+b*c) d b+
      fourRowThreePhi (a+b+c) (a*b+a*c+b*c) d c =
      fourRowThreeDenominator (a+b+c) (a*b+a*c+b*c) d := by
  unfold fourRowThreePhi fourRowThreeDenominator
  ring

theorem fourRowThreeStationary_sum (a b c d : ℝ)
    (hden : fourRowThreeDenominator (a+b+c) (a*b+a*c+b*c) d ≠ 0) :
    (∑ i, fourRowThreeStationary a b c d i) = 1 := by
  simp only [fourRowThreeStationary]
  norm_num [Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three]
  rw [←add_div,←add_div]
  rw [←add_assoc,fourRowThreePhi_mass]
  exact div_self hden

/-- Equality of the three actual active partial derivatives. -/
theorem fourRowThreeStationary_gradient (a b c d : ℝ)
    (hden : fourRowThreeDenominator (a+b+c) (a*b+a*c+b*c) d ≠ 0) :
    let v := fourRowThreeStationary a b c d
    let r : Fin 4 → ℝ := ![a,b,c,d]
    (fourRowGaugeCollision r 0-4*(a+b+c+d)*(v 1*c*d+v 2*b*d) =
      fourRowGaugeCollision r 1-4*(a+b+c+d)*(v 0*c*d+v 2*a*d)) ∧
    (fourRowGaugeCollision r 0-4*(a+b+c+d)*(v 1*c*d+v 2*b*d) =
      fourRowGaugeCollision r 2-4*(a+b+c+d)*(v 0*b*d+v 1*a*d)) := by
  dsimp only
  simp only [fourRowThreeStationary,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two]
  norm_num [fourRowGaugeCollision,fourRowThreeStationary,
    Fin.sum_univ_succ,Finset.sum_erase,Fin.ext_iff,-Fin.val_eq_zero_iff,
    Matrix.cons_val_two,Matrix.cons_val_three]
  generalize hQ : fourRowThreeDenominator (a+b+c) (a*b+a*c+b*c) d = Q at hden ⊢
  constructor <;> field_simp [hden]
  all_goals rw [←hQ]
  all_goals unfold fourRowThreePhi fourRowThreeDenominator
  all_goals ring

set_option maxHeartbeats 4000000 in
/-- The actual stationary objective, including its exact fixed-moment affine-product form. -/
theorem fourRowThreeStationary_value (a b c d : ℝ)
    (hden : fourRowThreeDenominator (a+b+c) (a*b+a*c+b*c) d ≠ 0) :
    fourRowMinorantHomogeneous ![a,b,c,d] (fourRowThreeStationary a b c d) =
      (fourRowThreeValueBase (a+b+c) (a*b+a*c+b*c) d+
        (a*b*c)*fourRowThreeValueSlope (a+b+c) (a*b+a*c+b*c) d)/
        fourRowThreeDenominator (a+b+c) (a*b+a*c+b*c) d := by
  norm_num [fourRowMinorantHomogeneous,fourRowGaugeCollision,fourRow_complement_product,
    fourRowThreeStationary,Fin.sum_univ_succ,Fin.prod_univ_succ,Finset.sum_erase,
    Fin.ext_iff,-Fin.val_eq_zero_iff,Matrix.cons_val_two,Matrix.cons_val_three]
  generalize hQ : fourRowThreeDenominator (a+b+c) (a*b+a*c+b*c) d = Q at hden ⊢
  field_simp [hden]
  rw [←hQ]
  unfold fourRowThreePhi fourRowThreeDenominator fourRowThreeValueBase fourRowThreeValueSlope
  ring

end DittertRybin
