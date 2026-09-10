import DR.Endpoint.TwoZeroReduction

namespace DittertRybin
open scoped BigOperators

example (a b c d : ℝ) :
    (averagePermanentRows (!![a,b;c,d]) 0 1).permanent =
      (a+c)*(b+d)/2 := by
  rw [averagePermanentRows_permanent _ _ _ (by decide)]
  norm_num [Matrix.permanent, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Matrix.updateRow_apply, ← Equiv.Perm.decomposeFin.symm.sum_comp,
    Fintype.sum_prod_type]
  ring

example : averagePermanentRows (!![1,0;0,1]) 0 1 =
    (!![(1/2:ℝ),1/2;1/2,1/2]) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [averagePermanentRows, Matrix.updateRow_apply]

example : orderThreeSquareSum (averagePermanentRows (!![1,0;0,1]) 0 1) = 1 := by
  rw [averagePermanentRows_norm _ _ _ (by decide)]
  norm_num [orderThreeSquareSum, Fin.sum_univ_succ]

/-- A repeated selected row is retained by the full permanent inequality. -/
example {n : ℕ} (A : Board (n+2) (n+2)) (hA : ∀ i j, 0 ≤ A i j) (a : Fin (n+2)) :
    (A.updateRow a (A a)).permanent*(A.updateRow a (A a)).permanent ≤ A.permanent^2 :=
  permanent_alexandrov_rows hA a a

example : ∃ A : Board 0 0, PermanentFaceMinimum (fun _ _ => False) A := by
  apply exists_permanentFaceMinimum
  refine ⟨0,?_,?_⟩
  · simp [mem_doublyStochastic_iff_sum]
  · intro i
    exact Fin.elim0 i

example : ¬∃ A : Board 1 1, PermanentFaceMinimum (fun _ _ => False) A := by
  rintro ⟨A,hA⟩
  have hz := hA.2.1 0 0 (by simp)
  have hr := sum_row_of_mem_doublyStochastic hA.1 0
  simp [hz] at hr

example (n : ℕ) : ∃ A : Board (n+2) (n+2),
    LeastNormPermanentFaceMinimum (twoZeroAllowed n) A :=
  exists_twoZero_leastNorm_minimum n

example {n : ℕ} (hn : 0 < n) (A : Board (n+2) (n+2))
    (hA : LeastNormPermanentFaceMinimum (twoZeroAllowed n) A) (i j : Fin n) :
    A i.succ.succ = A j.succ.succ := hA.twoZero_ordinary_rows hn i j

example {n : ℕ} (hn : 0 < n) (A : Board (n+2) (n+2))
    (hA : LeastNormPermanentFaceMinimum (twoZeroAllowed n) A) (i j : Fin n)
    (r : Fin (n+2)) : A r i.succ.succ = A r j.succ.succ :=
  hA.twoZero_ordinary_columns hn i j r

example : twoZeroReducedBoard 2 (1/2) 0 0 0 = 0 := by norm_num [twoZeroReducedBoard]
example : twoZeroReducedBoard 2 0 (1/2) 1 1 = 0 := by norm_num [twoZeroReducedBoard]

/-- The reduction accepts arbitrary independent zeros and every additional zero. -/
example {n : ℕ} (hn : 0 < n) (D : Board (n+2) (n+2))
    (hD : D ∈ doublyStochastic ℝ (Fin (n+2)))
    (i₁ i₂ j₁ j₂ : Fin (n+2)) (hi : i₁ ≠ i₂) (hj : j₁ ≠ j₂)
    (hz₁ : D i₁ j₁ = 0) (hz₂ : D i₂ j₂ = 0) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ 1/(n : ℝ) ∧ 0 ≤ b ∧ b ≤ 1/(n : ℝ) ∧
      (twoZeroReducedBoard n a b).permanent ≤ D.permanent :=
  twoZeroReducedBoard_representative hn hD i₁ i₂ j₁ j₂ hi hj hz₁ hz₂

#print axioms permanent_alexandrov_rows
#print axioms averagePermanentRows_permanent
#print axioms averagePermanentRows_norm
#print axioms PermanentFaceMinimum.average_rows_permanent
#print axioms averagePermanentRows_mem_face
#print axioms isCompact_permanentFace
#print axioms exists_leastNormPermanentFaceMinimum
#print axioms LeastNormPermanentFaceMinimum.equal_rows
#print axioms LeastNormPermanentFaceMinimum.twoZero_ordinary_columns
#print axioms LeastNormPermanentFaceMinimum.twoZero_reduced_form
#print axioms twoZeroReducedBoard_representative

end DittertRybin
