import DR.Endpoint.PermanentFaceDirections
import DR.Endpoint.PermanentCofactorAlgebra
import Mathlib.GroupTheory.Perm.Fin

namespace DittertRybin.Tests
open scoped BigOperators
open Matrix

-- The omitted factor is absent even at a zero or signed one-cell matrix.
example (a : ℝ) : permanentalCofactor (fun _ _ : Unit => a) () () = 1 := by
  simp [permanentalCofactor]
example : permanentalCofactor (fun _ _ : Unit => (-2 : ℝ)) () () = 1 := by
  simp [permanentalCofactor]

-- A zero off-diagonal cofactor need not equal the permanent on a restricted face.
example : permanentalCofactor (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by
  rw [permanentalCofactor, ← Equiv.Perm.decomposeFin.symm.sum_comp]
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ]
  rw [show Finset.univ.erase (1 : Fin 2) = {0} by decide]
  simp
example : ¬permanentalCofactor (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
    Matrix.permanent (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [permanentalCofactor, ← Equiv.Perm.decomposeFin.symm.sum_comp]
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ]
  rw [show Finset.univ.erase (1 : Fin 2) = {0} by decide]
  simp

example (A E : Matrix (Fin 0) (Fin 0) ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.permanent (fun i j => A i j+t*E i j)) 0 0 := by
  simpa using hasDerivAt_permanent_line A E
example (A : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ j, A 1 j*permanentalCofactor A 1 j) = A.permanent :=
  permanentalCofactor_row_euler A 1
example (A : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ i, A i 2*permanentalCofactor A i 2) = A.permanent :=
  permanentalCofactor_column_euler A 2

example {ι : Type*} [Fintype ι] [DecidableEq ι] (allowed : ι → ι → Prop)
    (A : Matrix ι ι ℝ) (hDS : A ∈ doublyStochastic ℝ ι)
    (hsupport : ∀ i j, ¬allowed i j → A i j = 0)
    (hmin : ∀ B : Matrix ι ι ℝ, B ∈ doublyStochastic ℝ ι →
      (∀ i j, ¬allowed i j → B i j = 0) → A.permanent ≤ B.permanent)
    (i j : ι) (hij : 0 < A i j) : permanentalCofactor A i j = A.permanent :=
  (show PermanentFaceMinimum allowed A from ⟨hDS, hsupport, hmin⟩).supported_cofactor i j hij

example (A : Matrix (Fin 3) (Fin 3) ℝ) (u : Fin 3 → ℝ) :
    (A.updateRow 1 u).permanent = ∑ j, u j*permanentalCofactor A 1 j :=
  permanent_updateRow_expansion A 1 u
example {allowed : Fin 3 → Fin 3 → Prop} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hmin : PermanentFaceMinimum allowed A) (hallowed : allowed 0 2)
    (hpos : 0 < permanentalCofactor A 0 2) : A.permanent ≤ permanentalCofactor A 0 2 :=
  hmin.allowed_cofactor_ge_of_pos 0 2 hallowed hpos
example {allowed : Fin 3 → Fin 3 → Prop} {A : Matrix (Fin 3) (Fin 3) ℝ}
    (hmin : PermanentFaceMinimum allowed A) (hallowed : allowed 0 2) :
    permanentalCofactor A 0 2 = 0 ∨ A.permanent ≤ permanentalCofactor A 0 2 :=
  hmin.allowed_cofactor_zero_or_ge 0 2 hallowed

#print axioms permanentalCofactor_contraction
#print axioms permanentalCofactor_row_euler
#print axioms permanentalCofactor_column_euler
#print axioms hasDerivAt_permanent_line
#print axioms PermanentFaceMinimum.cofactorLine_localMin
#print axioms PermanentFaceMinimum.supported_cofactor
#print axioms PermanentFaceMinimum.direction_nonneg
#print axioms PermanentFaceMinimum.allowed_cofactor_ge_of_pos
#print axioms PermanentFaceMinimum.allowed_cofactor_zero_or_ge
#print axioms permanentalCofactor_transpose

end DittertRybin.Tests
