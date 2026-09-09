import DR.Endpoint.RowDeletionRook
import DR.Endpoint.RowDeletionExpectation
import DR.Collision.Averaging

/-! Exact conjugacy between the actual endpoint blend kernel and the
expected two-row deletion matrix. The underlying law is normalizeRows P,
including when P is itself obtained by deleting columns from another board. -/

namespace DittertRybin
open scoped BigOperators
open Certificates
set_option backward.isDefEq.respectTransparency false

theorem rowDeletionExpectation_eq_event {m n : ℕ} (X : Board m n) (a b : Fin m) :
    rowDeletionExpectation X a b=
      if a=b then 0 else rowAssignmentEvent X {z | RowsDistinctOutside {a,b} z} := by
  classical
  by_cases hab : a=b
  · subst b
    simp [rowDeletionExpectation,rowDeletionMatrix_self]
  · simp only [if_neg hab,rowDeletionExpectation,rowAssignmentEvent]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hd : RowsDistinctOutside {a,b} z <;> simp [rowDeletionMatrix,hab,hd]

theorem rowMass_product_delete_pair {m n : ℕ} (P : Board m n)
    (a b : Fin m) (hab : a≠b) :
    rowSum P a*rowSum P b*(∏ i∈Finset.univ\({a,b} : Finset (Fin m)),rowSum P i)=
      ∏ i,rowSum P i := by
  have h := Finset.prod_sdiff (f := rowSum P)
    (Finset.subset_univ ({a,b} : Finset (Fin m)))
  rw [Finset.prod_pair hab] at h
  calc
    _ = (∏ i∈Finset.univ\({a,b} : Finset (Fin m)),rowSum P i)*(rowSum P a*rowSum P b) := by ring
    _ = _ := h

/-- Row-mass conjugation of the actual matching-exclusion kernel. -/
theorem matchingExclusionKernel_rowMass_conjugacy {m n : ℕ} (P : Board m n)
    (hr : ∀ i,rowSum P i≠0) (a b : Fin m) :
    rowSum P a*rowSum P b*matchingExclusionKernel P (m-2) a b=
      (∏ i,rowSum P i)*rowDeletionExpectation (normalizeRows P) a b := by
  classical
  by_cases hab : a=b
  · subst b
    simp [matchingExclusionKernel,rowDeletionExpectation,rowDeletionMatrix_self]
  · have hk : (Finset.univ\({a,b} : Finset (Fin m))).card=m-2 := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,
        Finset.card_pair hab]
    rw [matchingExclusionKernel,if_neg hab,rookSum_eraseRows_normalized P hr {a,b} hk,
      rowDeletionExpectation_eq_event,if_neg hab]
    rw [← mul_assoc,rowMass_product_delete_pair P a b hab]

theorem averagingKernel_rowMass_conjugacy {m n : ℕ} (P : Board m n)
    (hr : ∀ i,rowSum P i≠0) (a b : Fin m) :
    rowSum P a*rowSum P b*averagingKernel P (m-2) a b=
      averagingCoefficient P (m-2)*rowSum P a*rowSum P b-
      (∏ i,rowSum P i)*rowDeletionExpectation (normalizeRows P) a b := by
  unfold averagingKernel
  rw [mul_sub,matchingExclusionKernel_rowMass_conjugacy P hr]
  ring

/-- With s_i=r_i/h, the coefficient of the actual expected deletion matrix
is product(r_i)/h². The identity remains exact on signed nonzero row masses. -/
theorem averagingKernel_normalized_row_conjugacy {m n : ℕ} (P : Board m n)
    (hr : ∀ i,rowSum P i≠0) (h : ℝ) (hh : h≠0) (a b : Fin m) :
    (rowSum P a/h)*(rowSum P b/h)*averagingKernel P (m-2) a b=
      averagingCoefficient P (m-2)*(rowSum P a/h)*(rowSum P b/h)-
      ((∏ i,rowSum P i)/h^2)*rowDeletionExpectation (normalizeRows P) a b := by
  have hc := averagingKernel_rowMass_conjugacy P hr a b
  field_simp [hh]
  nlinarith only [hc]

/-- The source coefficient gamma = h^(m-2) product(s_i) is exactly
product(r_i)/h² when s_i=r_i/h. No factorial is present. -/
theorem normalizedRow_product_coefficient {m : ℕ} (hm : 2≤m)
    (r : Fin m → ℝ) (h : ℝ) (hh : h≠0) :
    h^(m-2)*(∏ i,r i/h)=(∏ i,r i)/h^2 := by
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  have hp : h^m=h^(m-2)*h^2 := by rw [← pow_add,Nat.sub_add_cancel hm]
  rw [hp]
  field_simp

/-- The exact actual-kernel quadratic identity after row normalization. -/
theorem averagingKernel_normalized_row_quadratic {m n : ℕ} (P : Board m n)
    (hr : ∀ i,rowSum P i≠0) (h : ℝ) (hh : h≠0) (x : Fin m → ℝ) :
    quadraticValue (averagingKernel P (m-2)) (fun i => (rowSum P i/h)*x i)=
      averagingCoefficient P (m-2)*(∑ i,(rowSum P i/h)*x i)^2-
      ((∏ i,rowSum P i)/h^2)*quadraticValue (rowDeletionExpectation (normalizeRows P)) x := by
  have he (i j : Fin m) :
      ((rowSum P i/h)*x i)*averagingKernel P (m-2) i j*((rowSum P j/h)*x j)=
      averagingCoefficient P (m-2)*((rowSum P i/h)*x i)*((rowSum P j/h)*x j)-
      ((∏ i,rowSum P i)/h^2)*(x i*rowDeletionExpectation (normalizeRows P) i j*x j) := by
    calc
      _ = x i*((rowSum P i/h)*(rowSum P j/h)*averagingKernel P (m-2) i j)*x j := by ring
      _ = _ := by rw [averagingKernel_normalized_row_conjugacy P hr h hh]; ring
  unfold quadraticValue
  simp only [he,Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum,← Finset.sum_mul]
  ring

end DittertRybin
