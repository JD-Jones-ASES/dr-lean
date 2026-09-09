import DR.Endpoint.RowDeletionKernel
import DR.Endpoint.RowLocalizedExpectation
import DR.Endpoint.CollisionSquareCompletion

/-! The actual endpoint blend kernel is positive definite once the
explicit localized scalar bounds are established. This is the conditional
matrix criterion; dimension-range estimates remain separate obligations. -/

namespace DittertRybin
open scoped BigOperators
open Certificates
set_option backward.isDefEq.respectTransparency false

/-- Scalar hypotheses of the localized collision criterion, evaluated on
the actual normalized row law of the supplied board. -/
structure EndpointCollisionKernelBounds {m n : ℕ} (P : Board m n) (h : ℝ) : Prop where
  row_deviation : (∑ i,(1-(m:ℝ)*(rowSum P i/h))^2)≤1/9
  mean_pair : (∑ i,rowLocalizedDoubletonLoad (normalizeRows P) i)/(m:ℝ)≤1/4
  centered_pair : (∑ i,(rowLocalizedDoubletonLoad (normalizeRows P) i-
    (∑ j,rowLocalizedDoubletonLoad (normalizeRows P) j)/(m:ℝ))^2)≤1/64
  deficit_two : ∀ i,rowLocalizedDeficitTwoLoad (normalizeRows P) i≤1/4
  coefficient : 4*(m:ℝ)^2≤averagingCoefficient P (m-2)/
    (((∏ i,rowSum P i)/h^2)*rowAvoidance (normalizeRows P))

theorem rowLocalizedDoubletonLoad_nonneg {m n : ℕ} (X : Board m n)
    (hX : ∀ i j,0≤X i j) (i : Fin m) : 0≤rowLocalizedDoubletonLoad X i := by
  unfold rowLocalizedDoubletonLoad
  apply Finset.sum_nonneg
  intro e he
  apply div_nonneg
  · exact rowAssignmentEvent_nonneg X hX _
  · exact rowAvoidance_nonneg X hX

/-- Quantitative lower bound for the actual kernel on row-scaled vectors. -/
theorem averagingKernel_endpoint_gap {m n : ℕ} (hm : 3≤m) (P : Board m n)
    (hP : ∀ i j,0≤P i j) (hr : ∀ i,0<rowSum P i) (h : ℝ) (hh : 0<h)
    (hp : 0<rowAvoidance (normalizeRows P)) (hB : EndpointCollisionKernelBounds P h)
    (x : Fin m → ℝ) :
    (3/32)*(((∏ i,rowSum P i)/h^2)*rowAvoidance (normalizeRows P))*(∑ i,x i^2)≤
      quadraticValue (averagingKernel P (m-2)) (fun i => (rowSum P i/h)*x i) := by
  let X := normalizeRows P
  let s : Fin m → ℝ := fun i => rowSum P i/h
  let t := rowLocalizedDoubletonLoad X
  let v := rowLocalizedDeficitTwoLoad X
  let p := rowAvoidance X
  let G := (∏ i,rowSum P i)/h^2
  let E := averagingCoefficient P (m-2)
  let sigma := E/(G*p)
  have hX : ∀ i j,0≤X i j := normalizeRows_nonneg P hP
  have hG : 0<G := div_pos (Finset.prod_pos (fun i _ => hr i)) (sq_pos_of_pos hh)
  have hgp : 0<G*p := mul_pos hG hp
  have ht : ∀ i,0≤t i := rowLocalizedDoubletonLoad_nonneg X hX
  have hc := endpoint_collision_lower_matrix_gap hm s t v sigma ht hB.row_deviation
    hB.mean_pair hB.centered_pair hB.deficit_two hB.coefficient x
  have hcw := mul_le_mul_of_nonneg_left hc hgp.le
  rw [endpointCollisionLowerMatrix_quadratic] at hcw
  have hdiag : (∑ i,(1+t i-2*v i)*x i^2)=
      (∑ i,x i^2)+(∑ i,t i*x i^2)-2*(∑ i,v i*x i^2) := by
    simp only [add_mul,sub_mul,one_mul,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    congr 1
    simp only [Finset.mul_sum,mul_assoc]
  rw [hdiag] at hcw
  have hl := rowDeletion_expectation_lower_localized X hX hp x
  have hlw := mul_le_mul_of_nonneg_left hl hG.le
  have heq := averagingKernel_normalized_row_quadratic P (fun i => (hr i).ne') h hh.ne' x
  have hcoef : (G*p)*sigma=E := by
    dsimp only [sigma]
    exact mul_div_cancel₀ E hgp.ne'
  have hcoefx := congrArg (fun a : ℝ => a*(∑ i,s i*x i)^2) hcoef
  change G*(p*((∑ i,x i^2)-(∑ i,x i)^2+(∑ i,t i*x i^2)-
    2*(∑ i,x i)*(∑ i,t i*x i)-2*(∑ i,v i*x i^2)))≤
      G*(-quadraticValue (rowDeletionExpectation X) x) at hlw
  change quadraticValue (averagingKernel P (m-2)) (fun i => s i*x i)=
    E*(∑ i,s i*x i)^2-G*quadraticValue (rowDeletionExpectation X) x at heq
  change (3/32)*(G*p)*(∑ i,x i^2)≤_
  nlinarith only [hcw,hlw,heq,hcoefx]

/-- Positive definiteness concerns the actual endpoint averaging kernel,
not a redefined quadratic functional or an assumed spectral floor. -/
theorem averagingKernel_endpoint_posDef {m n : ℕ} (hm : 3≤m) (P : Board m n)
    (hP : ∀ i j,0≤P i j) (hr : ∀ i,0<rowSum P i) (h : ℝ) (hh : 0<h)
    (hp : 0<rowAvoidance (normalizeRows P)) (hB : EndpointCollisionKernelBounds P h) :
    (averagingKernel P (m-2)).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.isHermitian_iff_isSymm]
    apply Matrix.IsSymm.ext
    exact fun i j => averagingKernel_symmetric P (m-2) j i
  · intro x hx
    let z : Fin m → ℝ := fun i => x i/(rowSum P i/h)
    have hs (i : Fin m) : rowSum P i/h≠0 := div_ne_zero (hr i).ne' hh.ne'
    have he : (fun i => (rowSum P i/h)*z i)=x := by
      funext i
      exact mul_div_cancel₀ (x i) (hs i)
    have hz : z≠0 := by
      intro hz
      apply hx
      rw [← he]
      simp only [hz,Pi.zero_apply,mul_zero]
      rfl
    have hzsq : 0<∑ i,z i^2 := by
      obtain ⟨i,hi⟩ := Function.ne_iff.mp hz
      have hi0 : z i≠0 := hi
      exact (sq_pos_of_ne_zero hi0).trans_le
        (Finset.single_le_sum (fun i _ => sq_nonneg (z i)) (Finset.mem_univ i))
    have hg := averagingKernel_endpoint_gap hm P hP hr h hh hp hB z
    rw [he] at hg
    have hc : 0<(3/32:ℝ)*(((∏ i,rowSum P i)/h^2)*rowAvoidance (normalizeRows P)) := by
      exact mul_pos (by norm_num) (mul_pos
        (div_pos (Finset.prod_pos (fun i _ => hr i)) (sq_pos_of_pos hh)) hp)
    have hpos := (mul_pos hc hzsq).trans_le hg
    simpa [quadraticValue_eq_dotProduct] using hpos

end DittertRybin
