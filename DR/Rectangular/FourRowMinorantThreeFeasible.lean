import DR.Rectangular.FourRowMinorantThreeStationary
import DR.Rectangular.FourRowMinorantThreeBoundary

/-! Feasible three-face stationary values are nonnegative, using the actual
compact fixed-moment reduction and the proved boundary/certificate inputs. -/

namespace DittertRybin
open scoped BigOperators

theorem threeMomentFeasible_rows_pos {s t : ℝ} {φ : ℝ → ℝ}
    {r : Fin 3 → ℝ} (hr : r ∈ threeMomentFeasible s t φ) (hD : 0 < 4*t-s^2) :
    ∀ i, 0 < r i := by
  have hs : r 0+r 1+r 2=s := by simpa [Fin.sum_univ_succ,add_assoc] using hr.2.1
  have ht := hr.2.2.1
  rw [←hs,←ht] at hD
  intro i
  by_contra hi
  have hz : r i = 0 := le_antisymm (le_of_not_gt hi) (hr.1 i)
  fin_cases i
  · change r 0=0 at hz
    rw [hz] at hD
    nlinarith [sq_nonneg (r 1-r 2)]
  · change r 1=0 at hz
    rw [hz] at hD
    nlinarith [sq_nonneg (r 0-r 2)]
  · change r 2=0 at hz
    rw [hz] at hD
    nlinarith [sq_nonneg (r 0-r 1)]

private theorem three_column_boundary (r v : Fin 4 → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hm : 0 < ∑ i, r i)
    (hv : ∀ i, 0 ≤ v i) (hvs : ∑ i, v i = 1) (h3 : v 3=0)
    (hz : ∃ i : Fin 3, v i.castSucc=0) : 0 ≤ fourRowMinorantHomogeneous r v := by
  obtain ⟨i,hi⟩ := hz
  fin_cases i
  · apply fourRowMinorantHomogeneous_pair_nonneg_of_pos_mass r v hr hm hv hvs 1 2 (by decide)
    intro k hk1 hk2
    fin_cases k <;> first | contradiction | exact hi | exact h3
  · apply fourRowMinorantHomogeneous_pair_nonneg_of_pos_mass r v hr hm hv hvs 0 2 (by decide)
    intro k hk0 hk2
    fin_cases k <;> first | contradiction | exact hi | exact h3
  · apply fourRowMinorantHomogeneous_pair_nonneg_of_pos_mass r v hr hm hv hvs 0 1 (by decide)
    intro k hk0 hk1
    fin_cases k <;> first | contradiction | exact hi | exact h3

private theorem stationary_numerator_nonneg_on_reduction {s t d : ℝ}
    (hd : 0 < d) (hD : 0 < 4*t-s^2) (r : Fin 3 → ℝ)
    (hr : r ∈ threeMomentFeasible s t (fourRowThreePhi s t d))
    (hcase : (∃ i, r i=0) ∨ (∃ i, fourRowThreePhi s t d (r i)=0) ∨
      r 0=r 1 ∨ r 0=r 2 ∨ r 1=r 2) :
    0 ≤ fourRowThreeValueBase s t d+fourRowThreeValueSlope s t d*(∏ i, r i) := by
  have hrp := threeMomentFeasible_rows_pos hr hD
  have hs : r 0+r 1+r 2=s := by simpa [Fin.sum_univ_succ,add_assoc] using hr.2.1
  have ht := hr.2.2.1
  have hsd : 0 < s+d := by linarith [hrp 0,hrp 1,hrp 2]
  have hden := fourRowThreeDenominator_pos hd hsd hD
  have hden' : fourRowThreeDenominator (r 0+r 1+r 2) (r 0*r 1+r 0*r 2+r 1*r 2) d ≠ 0 := by
    simpa [hs,ht] using hden.ne'
  let R : Fin 4 → ℝ := ![r 0,r 1,r 2,d]
  let v := fourRowThreeStationary (r 0) (r 1) (r 2) d
  have hR : ∀ i, 0 < R i := by
    intro i
    fin_cases i
    · exact hrp 0
    · exact hrp 1
    · exact hrp 2
    · exact hd
  have hv : ∀ i, 0 ≤ v i := by
    intro i
    fin_cases i
    · exact div_nonneg (by simpa [hs,ht] using hr.2.2.2 0) (by simpa [hs,ht] using hden.le)
    · exact div_nonneg (by simpa [hs,ht] using hr.2.2.2 1) (by simpa [hs,ht] using hden.le)
    · exact div_nonneg (by simpa [hs,ht] using hr.2.2.2 2) (by simpa [hs,ht] using hden.le)
    · exact le_rfl
  have hvs : ∑ i, v i=1 := fourRowThreeStationary_sum _ _ _ _ hden'
  have hv3 : v 3=0 := rfl
  have hH : 0 ≤ fourRowMinorantHomogeneous R v := by
    rcases hcase with hzero | hphi | hrep
    · obtain ⟨i,hi⟩ := hzero
      exact False.elim ((hrp i).ne' hi)
    · apply three_column_boundary R v (fun i => (hR i).le)
        (Finset.sum_pos (fun i _ => hR i) Finset.univ_nonempty) hv hvs hv3
      obtain ⟨i,hi⟩ := hphi
      refine ⟨i,?_⟩
      fin_cases i
      · change fourRowThreePhi s t d (r 0)=0 at hi
        simp [v,fourRowThreeStationary,hs,ht,hi]
      · change fourRowThreePhi s t d (r 1)=0 at hi
        simp [v,fourRowThreeStationary,hs,ht,hi]
      · change fourRowThreePhi s t d (r 2)=0 at hi
        simp [v,fourRowThreeStationary,Matrix.cons_val_two,hs,ht,hi]
    · exact fourRowMinorantHomogeneous_repeated_active_nonneg R v hR hv hvs hv3 hrep
  have hvalue := fourRowThreeStationary_value (r 0) (r 1) (r 2) d hden'
  change fourRowMinorantHomogeneous R v = _ at hvalue
  rw [hvalue,hs,ht] at hH
  have hnum := (le_div_iff₀ hden).mp hH
  have hp : (∏ i, r i)=r 0*r 1*r 2 := by simp [Fin.prod_univ_succ,mul_assoc]
  rw [hp]
  nlinarith [hnum]

/-- Every feasible stationary point on a proper three-coordinate face has
nonnegative actual minorant value. The compact reduction is proved above;
the stationary feasibility premise is explicit and indispensable. -/
theorem fourRowThreeStationary_feasible_nonneg (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d)
    (hD : 0 < 4*(a*b+a*c+b*c)-(a+b+c)^2)
    (hfeas : ∀ i, 0 ≤ fourRowThreeStationary a b c d i) :
    0 ≤ fourRowMinorantHomogeneous ![a,b,c,d] (fourRowThreeStationary a b c d) := by
  let s := a+b+c
  let t := a*b+a*c+b*c
  let φ := fourRowThreePhi s t d
  have hsd : 0 < s+d := by dsimp [s]; positivity
  have hden := fourRowThreeDenominator_pos hd hsd hD
  have hφ : Continuous φ := by
    change Continuous (fun x => fourRowThreePhi s t d x)
    unfold fourRowThreePhi
    fun_prop
  have hin : (![a,b,c] : Fin 3 → ℝ) ∈ threeMomentFeasible s t φ := by
    refine ⟨?_,?_,rfl,?_⟩
    · intro i; fin_cases i <;> assumption
    · simp [s,Fin.sum_univ_succ,add_assoc]
    · intro i
      have hi := hfeas i.castSucc
      fin_cases i
      all_goals
        convert! (le_div_iff₀ hden).mp hi using 1
        simp
  obtain ⟨r,hr,hmin,hcase⟩ := threeMomentFeasible_exists_affine_minimum s t
    (fourRowThreeValueBase s t d) (fourRowThreeValueSlope s t d) φ hφ ⟨![a,b,c],hin⟩
  have hnum := stationary_numerator_nonneg_on_reduction hd hD r hr hcase
  have hnum0 := hnum.trans (hmin _ hin)
  rw [fourRowThreeStationary_value a b c d hden.ne']
  apply div_nonneg _ hden.le
  simpa [Fin.prod_univ_succ,mul_comm,mul_left_comm,mul_assoc] using hnum0

end DittertRybin
