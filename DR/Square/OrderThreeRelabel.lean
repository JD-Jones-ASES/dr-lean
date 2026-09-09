import DR.Square.OrderThreeSymmetry

/-! Exact row and column relabeling invariance for square Dittert matrices. -/

open scoped BigOperators

namespace DittertRybin

theorem totalMass_permuted_square {n : ℕ} (A : Board n n)
    (r c : Equiv.Perm (Fin n)) : totalMass (A.submatrix r c) = totalMass A := by
  have hrow (i) : rowSum (A.submatrix r c) i = rowSum A (r i) :=
    Equiv.sum_comp c (fun j => A (r i) j)
  simp only [totalMass, hrow]
  exact Equiv.sum_comp r (rowSum A)

theorem dittertFunctional_permuted_square {n : ℕ} (A : Board n n)
    (r c : Equiv.Perm (Fin n)) : dittertFunctional (A.submatrix r c) = dittertFunctional A := by
  have hp : (A.submatrix r c).permanent = A.permanent := by
    calc
      _ = ((A.submatrix r id).submatrix id c).permanent := rfl
      _ = (A.submatrix r id).permanent := Matrix.permanent_permute_rows c _
      _ = _ := Matrix.permanent_permute_cols r A
  have hrow (i) : rowSum (A.submatrix r c) i = rowSum A (r i) :=
    Equiv.sum_comp c (fun j => A (r i) j)
  have hcol (j) : colSum (A.submatrix r c) j = colSum A (c j) :=
    Equiv.sum_comp r (fun i => A i (c j))
  simp only [dittertFunctional, hrow, hcol, hp, Equiv.prod_comp]

theorem dittert_globalMax_permuted_square {n : ℕ} {A : Board n n}
    (hmax : ∀ B : Board n n, (∀ i j, 0 ≤ B i j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional A) (r c : Equiv.Perm (Fin n)) :
    ∀ B : Board n n, (∀ i j, 0 ≤ B i j) → totalMass B = n →
      dittertFunctional B ≤ dittertFunctional (A.submatrix r c) := by
  simpa only [dittertFunctional_permuted_square] using hmax

theorem square_uniform_of_permuted_uniform {n : ℕ} {A : Board n n}
    (r c : Equiv.Perm (Fin n)) (h : A.submatrix r c = uniformDittertMatrix n) :
    A = uniformDittertMatrix n := by
  ext i j
  have hij := congrFun (congrFun h (r.symm i)) (c.symm j)
  simpa [Matrix.submatrix_apply, uniformDittertMatrix] using hij

end DittertRybin
