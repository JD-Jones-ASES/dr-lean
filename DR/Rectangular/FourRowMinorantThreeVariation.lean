import DR.Rectangular.FourRowMinorantThreeMinimum
import DR.Rectangular.FourRowMinorantStationaryMin

/-! The actual three-face minimizing vector has positive discriminant and
equals the source's feasible stationary vector. Flat directions are ruled
out by the proved maximum-norm choice among equal minima. -/

namespace DittertRybin
open scoped BigOperators

noncomputable def fourRowThreeConcentrationDirection (a b c : ℝ) : Fin 4 → ℝ :=
  let s := a+b+c
  let q := a^2+b^2+c^2
  ![a*(q-s*a),b*(q-s*b),c*(q-s*c),0]

theorem fourRowThreeConcentrationDirection_sum (a b c : ℝ) :
    (∑ i,fourRowThreeConcentrationDirection a b c i)=0 := by
  norm_num [fourRowThreeConcentrationDirection,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_three]
  ring

theorem fourRowThreeConcentrationDirection_quadratic (a b c d : ℝ) :
    fourRowMinorantQuadratic ![a,b,c,d] (fourRowThreeConcentrationDirection a b c) =
      2*(a+b+c+d)*(a*b*c*d)*(3*(a^2+b^2+c^2)-(a+b+c)^2)*
        (4*(a*b+a*c+b*c)-(a+b+c)^2) := by
  norm_num [fourRowMinorantQuadratic,fourRowThreeConcentrationDirection,fourRow_complement_product,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Finset.sum_erase,Fin.ext_iff,
    -Fin.val_eq_zero_iff,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

/-- The actual selected minimizer forces the strict discriminant inequality,
including exclusion of the singular D=0 case. -/
theorem IsThreeFaceMinorantMinimum.discriminant_pos {a b c d : ℝ} {v : Fin 4 → ℝ}
    (hmin : IsThreeFaceMinorantMinimum ![a,b,c,d] v)
    (htie : IsThreeFaceMinorantMaxNormTie ![a,b,c,d] v)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hv : ∀ i, i ≠ 3 → 0 < v i) (hvs : ∑ i,v i=1) (hv3 : v 3=0) :
    0 < 4*(a*b+a*c+b*c)-(a+b+c)^2 := by
  by_contra hD
  have hDle := le_of_not_gt hD
  have hs : 0 < a+b+c := by positivity
  have hK : 0 < 3*(a^2+b^2+c^2)-(a+b+c)^2 := by
    nlinarith [sq_pos_of_pos hs]
  have hf : 0 < 2*(a+b+c+d)*(a*b*c*d)*(3*(a^2+b^2+c^2)-(a+b+c)^2) := by positivity
  have hQ := hmin.quadratic_nonneg hv hvs hv3 _ (fourRowThreeConcentrationDirection_sum a b c) rfl
  rw [fourRowThreeConcentrationDirection_quadratic] at hQ
  have hDge := nonneg_of_mul_nonneg_right hQ hf
  have hD0 := le_antisymm hDle hDge
  have hQ0 : fourRowMinorantQuadratic ![a,b,c,d] (fourRowThreeConcentrationDirection a b c)=0 := by
    rw [fourRowThreeConcentrationDirection_quadratic,hD0,mul_zero]
  have hw := htie.quadratic_zero hmin hv hvs hv3 _
    (fourRowThreeConcentrationDirection_sum a b c) rfl hQ0
  have hwa := congrFun hw 0
  have hwb := congrFun hw 1
  have hwc := congrFun hw 2
  change a*((a^2+b^2+c^2)-(a+b+c)*a)=0 at hwa
  change b*((a^2+b^2+c^2)-(a+b+c)*b)=0 at hwb
  change c*((a^2+b^2+c^2)-(a+b+c)*c)=0 at hwc
  have heqa := sub_eq_zero.mp ((mul_eq_zero.mp hwa).resolve_left ha.ne')
  have heqb := sub_eq_zero.mp ((mul_eq_zero.mp hwb).resolve_left hb.ne')
  have heqc := sub_eq_zero.mp ((mul_eq_zero.mp hwc).resolve_left hc.ne')
  have hab : a=b := (mul_left_cancel₀ hs.ne') (heqa.symm.trans heqb)
  have hac : a=c := (mul_left_cancel₀ hs.ne') (heqa.symm.trans heqc)
  rw [←hab,←hac] at hD0
  nlinarith [sq_pos_of_pos ha]

theorem fourRowMinorantGradient_three_active (a b c d : ℝ) (v : Fin 4 → ℝ)
    (hv3 : v 3=0) :
    (fourRowMinorantGradient ![a,b,c,d] v 0 =
      fourRowGaugeCollision ![a,b,c,d] 0-4*(a+b+c+d)*(v 1*c*d+v 2*b*d)) ∧
    (fourRowMinorantGradient ![a,b,c,d] v 1 =
      fourRowGaugeCollision ![a,b,c,d] 1-4*(a+b+c+d)*(v 0*c*d+v 2*a*d)) ∧
    (fourRowMinorantGradient ![a,b,c,d] v 2 =
      fourRowGaugeCollision ![a,b,c,d] 2-4*(a+b+c+d)*(v 0*b*d+v 1*a*d)) := by
  refine ⟨?_,?_,?_⟩
  all_goals
    norm_num [fourRowMinorantGradient,fourRow_complement_product,Fin.sum_univ_succ,
      Fin.prod_univ_succ,Finset.sum_erase,Fin.ext_iff,-Fin.val_eq_zero_iff,
      Matrix.cons_val_two,Matrix.cons_val_three]
  all_goals simp only [show Fin.succ (2 : Fin 3)=(3 : Fin 4) from rfl,hv3]
  all_goals ring

theorem fourRowThreeStationary_gradient_dot (a b c d : ℝ)
    (hden : fourRowThreeDenominator (a+b+c) (a*b+a*c+b*c) d ≠ 0)
    (w : Fin 4 → ℝ) (hws : ∑ i,w i=0) (hw3 : w 3=0) :
    (∑ i,fourRowMinorantGradient ![a,b,c,d] (fourRowThreeStationary a b c d) i*w i)=0 := by
  let v := fourRowThreeStationary a b c d
  have hv3 : v 3=0 := rfl
  obtain ⟨hg0,hg1,hg2⟩ := fourRowMinorantGradient_three_active a b c d v hv3
  have hstat := fourRowThreeStationary_gradient a b c d hden
  change _ ∧ _ at hstat
  have h01 : fourRowMinorantGradient ![a,b,c,d] v 0=fourRowMinorantGradient ![a,b,c,d] v 1 := by
    rw [hg0,hg1]
    exact hstat.1
  have h02 : fourRowMinorantGradient ![a,b,c,d] v 0=fourRowMinorantGradient ![a,b,c,d] v 2 := by
    rw [hg0,hg2]
    exact hstat.2
  have hws' : w 0+w 1+w 2=0 := by
    simpa [Fin.sum_univ_succ,hw3,add_assoc] using hws
  change (∑ i,fourRowMinorantGradient ![a,b,c,d] v i*w i)=0
  simp only [Fin.sum_univ_four,hw3,mul_zero,add_zero,←h01,←h02]
  rw [←mul_add,←mul_add,hws',mul_zero]

/-- The explicit stationary vector is derived from an actual selected minimum,
without assuming its feasibility or identifying it with the minimizer in advance. -/
theorem IsThreeFaceMinorantMinimum.eq_stationary {a b c d : ℝ} {v : Fin 4 → ℝ}
    (hmin : IsThreeFaceMinorantMinimum ![a,b,c,d] v)
    (htie : IsThreeFaceMinorantMaxNormTie ![a,b,c,d] v)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hv : ∀ i, i ≠ 3 → 0 < v i) (hvs : ∑ i,v i=1) (hv3 : v 3=0) :
    v=fourRowThreeStationary a b c d := by
  have hD := hmin.discriminant_pos htie ha hb hc hd hv hvs hv3
  have hden := fourRowThreeDenominator_pos hd (by positivity : 0 < a+b+c+d) hD
  let vstar := fourRowThreeStationary a b c d
  let w := fun i => v i-vstar i
  have hws : (∑ i,w i)=0 := by
    simp only [w,Finset.sum_sub_distrib,hvs,fourRowThreeStationary_sum _ _ _ _ hden.ne',vstar]
    ring
  have hw3 : w 3=0 := by simp [w,vstar,fourRowThreeStationary,hv3]
  have hg := hmin.gradient_dot_zero hv hvs hv3 w hws hw3
  have hgstar := fourRowThreeStationary_gradient_dot a b c d hden.ne' w hws hw3
  change (∑ i,fourRowMinorantGradient ![a,b,c,d] vstar i*w i)=0 at hgstar
  have hdiff := fourRowMinorant_gradient_difference_dot ![a,b,c,d] vstar w
  have heq : (fun i => vstar i+w i)=v := by funext i; simp [w]
  rw [heq] at hdiff
  simp only [sub_mul,Finset.sum_sub_distrib,hg,hgstar,sub_self] at hdiff
  have hQ : fourRowMinorantQuadratic ![a,b,c,d] w=0 := by linarith
  have hw := htie.quadratic_zero hmin hv hvs hv3 w hws hw3 hQ
  funext i
  exact sub_eq_zero.mp (congrFun hw i)

end DittertRybin
