import DR.Square.HomogeneousDittert
import DR.Square.BlockFloor

/-! Homogeneous lower-order Dittert bounds on independently labeled cut blocks. -/

namespace DittertRybin
open scoped BigOperators

theorem DittertMaximizer.permanent_lower_fintype {ι : Type*}
    [Fintype ι] [DecidableEq ι] (hD : DittertMaximizer (Fintype.card ι))
    (hn : 0 < Fintype.card ι) (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) :
    (∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) -
      (2-dittertConstant (Fintype.card ι)) *
        ((∑ i, ∑ j, A i j) / Fintype.card ι)^(Fintype.card ι) ≤ A.permanent := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have h := hD.permanent_lower hn (A.submatrix e e) (fun i j => hA (e i) (e j))
  have hr (i : Fin (Fintype.card ι)) : rowSum (A.submatrix e e) i = ∑ j, A (e i) j :=
    Equiv.sum_comp e (fun j => A (e i) j)
  have hc (j : Fin (Fintype.card ι)) : colSum (A.submatrix e e) j = ∑ i, A i (e j) :=
    Equiv.sum_comp e (fun i => A i (e j))
  have hR : (∏ i, rowSum (A.submatrix e e) i) = ∏ i, ∑ j, A i j := by
    simp_rw [hr]
    exact Equiv.prod_comp e (fun i => ∑ j, A i j)
  have hC : (∏ j, colSum (A.submatrix e e) j) = ∏ j, ∑ i, A i j := by
    simp_rw [hc]
    exact Equiv.prod_comp e (fun j => ∑ i, A i j)
  have hM : totalMass (A.submatrix e e) = ∑ i, ∑ j, A i j := by
    unfold totalMass
    simp_rw [hr]
    exact Equiv.sum_comp e (fun i => ∑ j, A i j)
  rw [hR, hC, hM, permanent_submatrix_equiv] at h
  exact h

/-- Direct application to the actual independently labeled row/column submatrix. -/
theorem DittertMaximizer.squareCutBlock_lower {n : ℕ}
    (A : Board n n) (hA : ∀ i j, 0 ≤ A i j) (I J : Finset (Fin n))
    (e : I ≃ J) (hI : 0 < I.card) (hD : DittertMaximizer I.card) :
    (∏ i : I, ∑ j ∈ J, A i j) + (∏ j : J, ∑ i ∈ I, A i j) -
      (2-dittertConstant I.card) * (cutMass A I J / I.card)^I.card ≤
        (squareCutBlock A I J e).permanent := by
  have hD' : DittertMaximizer (Fintype.card I) := by simpa using hD
  have h := hD'.permanent_lower_fintype (by simpa using hI)
    (squareCutBlock A I J e) (fun i j => hA i (e j))
  rw [squareCutBlock_totalMass] at h
  simp only [squareCutBlock_sum_row, squareCutBlock_sum_col, Fintype.card_coe] at h
  have hC : (∏ j : I, ∑ i ∈ I, A i (e j)) = ∏ j : J, ∑ i ∈ I, A i j :=
    Equiv.prod_comp e (fun j : J => ∑ i ∈ I, A i j)
  rw [hC] at h
  exact h

end DittertRybin
