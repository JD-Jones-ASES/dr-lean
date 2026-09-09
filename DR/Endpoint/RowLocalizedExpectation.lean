import DR.Endpoint.RowDeficitLocalization

/-! The actual deletion expectation lower bound in the exact localized
ratios used by the collision estimates. -/

namespace DittertRybin
open scoped BigOperators
open Certificates

theorem rowDeletion_expectation_lower_localized {m n : ℕ} (X : Board m n)
    (hX : ∀ i j,0≤X i j) (hp : 0<rowAvoidance X) (x : Fin m → ℝ) :
    rowAvoidance X*((∑ i,x i^2)-(∑ i,x i)^2+
      (∑ i,rowLocalizedDoubletonLoad X i*x i^2)-
      2*(∑ i,x i)*(∑ i,rowLocalizedDoubletonLoad X i*x i)-
      2*(∑ i,rowLocalizedDeficitTwoLoad X i*x i^2)) ≤
        -quadraticValue (rowDeletionExpectation X) x := by
  have hu (i : Fin m) : rowDoubletonParticipationMass X i=
      rowAvoidance X*rowLocalizedDoubletonLoad X i := by
    have h := rowDoubletonParticipationMass_div X i
    exact (div_eq_iff hp.ne').mp h |>.trans (mul_comm _ _)
  have hv (i : Fin m) : rowDeficitTwoParticipationMass X i≤
      rowAvoidance X*rowLocalizedDeficitTwoLoad X i := by
    have h := (div_le_iff₀ hp).mp (rowDeficitTwoParticipationMass_div_le X hX hp i)
    exact h.trans_eq (mul_comm _ _)
  have hvsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    mul_le_mul_of_nonneg_right (hv i) (sq_nonneg (x i)))
  have h := rowDeletion_expectation_lower X hX x
  simp_rw [hu] at h
  have he1 : (∑ i,(rowAvoidance X*rowLocalizedDoubletonLoad X i)*x i^2)=
      rowAvoidance X*(∑ i,rowLocalizedDoubletonLoad X i*x i^2) := by
    simp only [Finset.mul_sum,mul_assoc]
  have he2 : (∑ i,(rowAvoidance X*rowLocalizedDoubletonLoad X i)*x i)=
      rowAvoidance X*(∑ i,rowLocalizedDoubletonLoad X i*x i) := by
    simp only [Finset.mul_sum,mul_assoc]
  have he3 : (∑ i,(rowAvoidance X*rowLocalizedDeficitTwoLoad X i)*x i^2)=
      rowAvoidance X*(∑ i,rowLocalizedDeficitTwoLoad X i*x i^2) := by
    simp only [Finset.mul_sum,mul_assoc]
  rw [he1,he2] at h
  rw [he3] at hvsum
  nlinarith only [h,hvsum]

end DittertRybin
