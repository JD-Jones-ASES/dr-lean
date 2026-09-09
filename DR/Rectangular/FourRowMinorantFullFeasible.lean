import DR.Rectangular.FourRowMinorantFullCompact
import DR.Rectangular.FourRowMinorantRowExtrema

/-! The full feasible stationary case. Its fixed-q compact maximum is an
actual row maximum, and the one-large structure is derived by exact feasible
curves before invoking the rational sign theorem. -/

namespace DittertRybin
open scoped BigOperators

theorem fourRowMinorantStationaryValue_fixed_objective (r : Fin 4 → ℝ) (q : ℝ)
    (hq : fourRowMinorantSquareSum r=q) (hd : 1-3*q ≠ 0) :
    fourRowMinorantStationaryValue r = (1-q)/8-(3/2)*
      fourRowMinorantRowObjective ((1-4*(1-3*q))/(9*(1-3*q))) r := by
  unfold fourRowMinorantStationaryValue fourRowMinorantRowObjective fourRowMinorantDelta
  rw [hq]
  generalize he : 1-3*q = D at hd ⊢
  field_simp [hd]
  ring

theorem fourRowMinorant_uniform_stationary_value :
    fourRowMinorantHomogeneous (fun _ => 1/4)
      (fourRowMinorantStationary (fun _ => 1/4)) = 0 := by
  norm_num [fourRowMinorantHomogeneous,fourRowMinorantStationary,fourRowMinorantSquareSum,
    fourRowMinorantDelta,fourRowGaugeCollision,fourRow_complement_product,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Finset.sum_erase,Fin.ext_iff,-Fin.val_eq_zero_iff]

/-- The actual full stationary vector has nonnegative objective whenever it
is feasible. Feasibility is retained at every compactness and shape step. -/
theorem fourRowMinorantStationary_feasible_nonneg (r : Fin 4 → ℝ)
    (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1)
    (hq : fourRowMinorantSquareSum r<1/3)
    (hv : ∀ i,0≤fourRowMinorantStationary r i) :
    0 ≤ fourRowMinorantHomogeneous r (fourRowMinorantStationary r) := by
  by_contra h
  have hneg := lt_of_not_ge h
  have hqlo := fourRowMinorantSquareSum_ge_quarter r hs
  have hqstrict : 1/4 < fourRowMinorantSquareSum r := by
    rcases lt_or_eq_of_le hqlo with hh | heq
    · exact hh
    · have hrconst := fourRowMinorant_rows_eq_quarter r hs heq.symm
      rw [hrconst,fourRowMinorant_uniform_stationary_value] at hneg
      exact False.elim (lt_irrefl _ hneg)
  let q := fourRowMinorantSquareSum r
  let γ := (1-4*(1-3*q))/(9*(1-3*q))
  have hd : 0 < 1-3*q := by dsimp [q]; linarith
  have hγ : 0 < γ := by
    apply div_pos _ (mul_pos (by norm_num) hd)
    dsimp [q]
    linarith
  have hvalue (u : Fin 4 → ℝ) (hus : ∑ i,u i=1) (huq : fourRowMinorantSquareSum u=q) :
      fourRowMinorantHomogeneous u (fourRowMinorantStationary u) =
        (1-q)/8-(3/2)*fourRowMinorantRowObjective γ u := by
    rw [fourRowMinorantStationary_value u hus
      (by simpa only [fourRowMinorantDelta,huq] using hd.ne')]
    exact fourRowMinorantStationaryValue_fixed_objective u q huq hd.ne'
  obtain ⟨u,hu,hus,huq,huv,humax,huobj⟩ := exists_fourRowMinorant_fixed_maximum γ r hr hs hv
  have huneg : fourRowMinorantHomogeneous u (fourRowMinorantStationary u)<0 := by
    rw [hvalue u hus huq]
    rw [hvalue r hs rfl] at hneg
    linarith
  have huqlo : 1/4 < fourRowMinorantSquareSum u := by rwa [huq]
  have huqhi : fourRowMinorantSquareSum u<1/3 := by rwa [huq]
  have hup := fourRowMinorant_rows_pos_of_squareSum_lt u hu hus huqhi
  have hvsum := fourRowMinorantStationary_sum u hus
  have hvp : ∀ i,0<fourRowMinorantStationary u i := by
    intro i
    by_contra hi
    have hi0 : fourRowMinorantStationary u i=0 := le_antisymm (le_of_not_gt hi) (huv i)
    have hb := fourRowMinorantHomogeneous_proper_face_nonneg u (fourRowMinorantStationary u)
      hu hus huv hvsum ⟨i,hi0⟩
    linarith
  obtain ⟨R,e,hR0,hR1,heq⟩ := humax.one_large hγ hup hus hvp huqlo huqhi
  have hstatperm : fourRowMinorantStationary (u ∘ e)=fourRowMinorantStationary u ∘ e := by
    funext i
    exact fourRowMinorantStationary_permute u e i
  have hpositive := fourRowMinorantOneLarge_value_pos R hR0 hR1
    (by rw [←heq,fourRowMinorantStationary_permute]; exact huv (e 0))
  rw [←heq,hstatperm,fourRowMinorantHomogeneous_permute] at hpositive
  linarith

end DittertRybin
