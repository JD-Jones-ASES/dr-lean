import DR.Endpoint.LeadingUniform
import DR.Endpoint.RowCollisionBounds
import DR.Endpoint.RowCollisionUnion

/-! The exact first-order collision correction for endpoint failure.
The proof uses the actual independent-row injection event and its union
bound. The rook normalization transfers it back to the original iid
functional with the exact factorial factor. Zero rows are treated directly. -/
namespace DittertRybin
open scoped BigOperators
open Certificates

theorem endpointLeadingColumnCost_sq {m n : ℕ} (hm : 3≤m) (P : Board m n)
    (hP : IsProbability P) (j : Fin n) :
    (endpointLeadingColumnCost P j)^2=
      quadraticValue (endpointLeadingKernel (rowSum P)) (fun i => P i j) := by
  apply Real.sq_sqrt
  have hb := endpointLeadingKernel_quadratic_bounds hm (rowSum P) (fun i => P i j)
    (rowSum_nonneg hP.1) hP.2 (fun i => hP.1 i j)
  exact (mul_nonneg (sub_nonneg.mpr (endpointLeadingDefect_bounds hm).2.le) (sq_nonneg _)).trans hb.1

/-- The normalized original-row collision intensity has its exact kernel coefficient. -/
theorem endpointLeading_cost_deficit_identity {m n : ℕ} (hm : 3≤m) (P : Board m n)
    (hP : IsProbability P) (hr : ∀ i,0<rowSum P i) :
    (∑ j,((colSum P j)^2-(endpointLeadingColumnCost P j)^2))=
      2*endpointLeadingScale (rowSum P)*rowCollisionIntensity (normalizeRows P) := by
  have hXS := normalizeRows_rowSum P (fun i => (hr i).ne')
  have hrec := endpointRowBoard_normalizeRows P (fun i => (hr i).ne')
  have he (j : Fin n) : (colSum P j)^2-(endpointLeadingColumnCost P j)^2=
      endpointLeadingScale (rowSum P)*endpointLeadingColumnCollision (normalizeRows P) j := by
    have h := endpointLeadingColumn_polynomial (rowSum P) (normalizeRows P) hXS j
    rw [hrec] at h
    have hc : (∑ i,rowSum P i*normalizeRows P i j)=colSum P j := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_div_cancel₀ (P i j) (hr i).ne'
    rw [hc,← endpointLeadingColumnCost_sq hm P hP j] at h
    linarith
  simp_rw [he]
  rw [← Finset.mul_sum]
  have hc : (∑ j,endpointLeadingColumnCollision (normalizeRows P) j)=
      2*rowCollisionIntensity (normalizeRows P) := by
    rw [rowCollisionIntensity_eq _ hXS]
    simp only [endpointLeadingColumnCollision,colSum,Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_comm
  rw [hc]
  ring

theorem endpoint_choose_two_factorial {m : ℕ} (hm : 2≤m) :
    (m.choose 2:ℝ)*2*((m-2).factorial:ℝ)=(m.factorial:ℝ) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 2
  have hc := congrArg (fun a : ℕ => (a:ℝ)) h
  simp only [Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.sub_zero,
    Nat.cast_mul,Nat.cast_sub (by omega : 1≤m),Nat.cast_one,mul_one] at hc
  norm_num [Nat.factorial] at hc
  rw [endpoint_leading_factorial_two hm]
  nlinarith only [hc]

/-- Exact first-order row-collision union bound, including a zero-row boundary. -/
theorem endpoint_row_failure_leading_bound {m n : ℕ} (hm : 3≤m) (P : Board m n)
    (hP : IsProbability P) :
    (m.factorial:ℝ)*((∏ i,rowSum P i)-rookSum P m)≤
      (m.choose 2:ℝ)*∑ j,((colSum P j)^2-(endpointLeadingColumnCost P j)^2) := by
  classical
  by_cases hr : ∀ i,0<rowSum P i
  · have h := one_sub_rowAvoidance_le_intensity (normalizeRows P)
      (normalizeRows_nonneg P hP.1) (normalizeRows_rowSum P (fun i => (hr i).ne'))
    have hprod : 0≤(m.factorial:ℝ)*∏ i,rowSum P i := by
      exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => (hr i).le))
    have hmul := mul_le_mul_of_nonneg_left h hprod
    rw [rookSum_endpoint_normalized P (fun i => (hr i).ne'),
      endpointLeading_cost_deficit_identity hm P hP hr]
    have hf := endpoint_choose_two_factorial (by omega : 2≤m)
    unfold endpointLeadingScale
    calc
      _=((m.factorial:ℝ)*∏ i,rowSum P i)*(1-rowAvoidance (normalizeRows P)) := by ring
      _≤((m.factorial:ℝ)*∏ i,rowSum P i)*rowCollisionIntensity (normalizeRows P) := hmul
      _=_ := by rw [← hf]; ring
  · obtain ⟨i,hi⟩ := not_forall.mp hr
    have hz : rowSum P i=0 := le_antisymm (le_of_not_gt hi) (rowSum_nonneg hP.1 i)
    have hprod : (∏ a,rowSum P a)=0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
    have hcost (j : Fin n) : (endpointLeadingColumnCost P j)^2=(colSum P j)^2 := by
      rw [endpointLeadingColumnCost_sq hm P hP j,endpointLeadingColumn_zero_row P hP.1 i hz j]
    simp only [hprod,hcost,sub_self,Finset.sum_const_zero,mul_zero,zero_sub,mul_neg]
    have hrook : 0≤rookSum P m := by
      rw [rookSum_endpoint_eq_rowAvoidance]
      exact rowAvoidance_nonneg P hP.1
    exact neg_nonpos.mpr (mul_nonneg (Nat.cast_nonneg _) hrook)

/-- The correction is for the actual iid failure probability and exact column marginal event. -/
theorem endpoint_failure_leading_lower {m n : ℕ} (hm : 3≤m) (P : Board m n)
    (hP : IsProbability P) :
    (1-(m.factorial:ℝ)*elementarySymmetric (colSum P) m)-
      (m.choose 2:ℝ)*∑ j,((colSum P j)^2-(endpointLeadingColumnCost P j)^2)≤
        1-separationProbability P m := by
  have h := endpoint_row_failure_leading_bound hm P hP
  rw [separationProbability_eq_rook,elementarySymmetric_top]
  linarith

end DittertRybin
