import DR.Rectangular.FourRowMinorantFaces
import DR.Rectangular.FourRowMinorantRepeated

/-! The certified repeated-row polynomial controls the entire corresponding
three-coordinate probability face, by exact averaging and positive scaling. -/

namespace DittertRybin
open scoped BigOperators

theorem fourRowMinorantHomogeneous_smul (r v : Fin 4 → ℝ) (c : ℝ) :
    fourRowMinorantHomogeneous (fun i => c*r i) v =
      c^3*fourRowMinorantHomogeneous r v := by
  norm_num [fourRowMinorantHomogeneous,fourRowGaugeCollision,fourRow_complement_product,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Finset.sum_erase,Fin.ext_iff,
    -Fin.val_eq_zero_iff]
  ring

/-- The exact averaging loss, with no positivity or normalization assumptions. -/
theorem fourRowMinorantHomogeneous_equal_rows_average (a b d T u w : ℝ) :
    fourRowMinorantHomogeneous ![a,b,b,d] ![T,u,w,0] =
      fourRowMinorantHomogeneous ![a,b,b,d] ![T,(u+w)/2,(u+w)/2,0]+
        (a+2*b+d)*a*d*(u-w)^2 := by
  norm_num [fourRowMinorantHomogeneous,fourRowGaugeCollision,fourRow_complement_product,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Finset.sum_erase,Fin.ext_iff,
    -Fin.val_eq_zero_iff,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

/-- Repeated positive row coordinates, arbitrary nonnegative total row mass,
and the full closed three-coordinate column face. -/
theorem fourRowMinorantHomogeneous_equal_rows_nonneg {a b d T u w : ℝ}
    (ha : 0 ≤ a) (hb : 0 < b) (hd : 0 ≤ d)
    (hT : 0 ≤ T) (hu : 0 ≤ u) (hw : 0 ≤ w) (hs : T+u+w=1) :
    0 ≤ fourRowMinorantHomogeneous ![a,b,b,d] ![T,u,w,0] := by
  have hT1 : T ≤ 1 := by linarith
  have huw : u+w = 1-T := by linarith
  have hr : (![a,b,b,d] : Fin 4 → ℝ) =
      fun i => b*(![a/b,1,1,d/b] : Fin 4 → ℝ) i := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_two,Matrix.cons_val_three]
    all_goals field_simp
  have hrep := fourRowMinorantHomogeneous_repeated_nonneg
    (div_nonneg ha hb.le) (div_nonneg hd hb.le) hT hT1
  have havg : 0 ≤ fourRowMinorantHomogeneous ![a,b,b,d] ![T,(u+w)/2,(u+w)/2,0] := by
    rw [huw,hr,fourRowMinorantHomogeneous_smul]
    exact mul_nonneg (pow_nonneg hb.le _) hrep
  rw [fourRowMinorantHomogeneous_equal_rows_average]
  exact add_nonneg havg (by positivity)

/-- Including zero repeated rows on the actual row probability simplex. -/
theorem fourRowMinorantHomogeneous_equal_rows_probability {a b d : ℝ}
    (v : Fin 4 → ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hrs : a+2*b+d=1) (hv : ∀ i, 0 ≤ v i) (hvs : ∑ i, v i = 1)
    (hv3 : v 3 = 0) :
    0 ≤ fourRowMinorantHomogeneous ![a,b,b,d] v := by
  by_cases hb0 : b = 0
  · refine fourRowMinorantHomogeneous_boundary_nonneg _ v ?_ ?_ hv hvs ⟨1,?_⟩
    · intro i; fin_cases i <;> simp [Matrix.cons_val_two,Matrix.cons_val_three,ha,hb,hd]
    · norm_num [Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three]
      linarith
    · exact hb0
  have hvvec : v = ![v 0,v 1,v 2,0] := by
    funext i
    fin_cases i <;> simp [Matrix.cons_val_two,Matrix.cons_val_three,hv3]
  have hs : v 0+v 1+v 2=1 := by
    simp [Fin.sum_univ_succ,hv3] at hvs
    linarith
  rw [hvvec]
  exact fourRowMinorantHomogeneous_equal_rows_nonneg ha (lt_of_le_of_ne hb (Ne.symm hb0))
    hd (hv 0) (hv 1) (hv 2) hs

end DittertRybin
