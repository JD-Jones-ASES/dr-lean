import DR.Endpoint.PermanentFaceCofactors

/-! Exact row and column replacement formulas for the actual permanent.
Cofactors are independent of their deleted row and column. -/

namespace DittertRybin
open scoped BigOperators
open Matrix

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem permanentalCofactor_updateCol (A : Matrix ι ι ℝ) (i j : ι) (u : ι → ℝ) :
    permanentalCofactor (A.updateCol j u) i j = permanentalCofactor A i j := by
  unfold permanentalCofactor
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs
  · apply Finset.prod_congr rfl
    intro k hk
    exact Matrix.updateCol_ne (Finset.mem_erase.mp hk).1
  · rfl

theorem permanentalCofactor_updateRow (A : Matrix ι ι ℝ) (i j : ι) (u : ι → ℝ) :
    permanentalCofactor (A.updateRow i u) i j = permanentalCofactor A i j := by
  unfold permanentalCofactor
  apply Finset.sum_congr rfl
  intro σ _
  split_ifs with hσ
  · apply Finset.prod_congr rfl
    intro k hk
    have hne : σ k ≠ i := by
      intro h
      exact (Finset.mem_erase.mp hk).1 (σ.injective (h.trans hσ.symm))
    simp only [Matrix.updateRow_ne hne]
  · rfl

theorem permanent_updateCol_expansion (A : Matrix ι ι ℝ) (j : ι) (u : ι → ℝ) :
    (A.updateCol j u).permanent = ∑ i, u i*permanentalCofactor A i j := by
  rw [← permanentalCofactor_column_euler (A.updateCol j u) j]
  simp only [Matrix.updateCol_self, permanentalCofactor_updateCol]

theorem permanent_updateRow_expansion (A : Matrix ι ι ℝ) (i : ι) (u : ι → ℝ) :
    (A.updateRow i u).permanent = ∑ j, u j*permanentalCofactor A i j := by
  rw [← permanentalCofactor_row_euler (A.updateRow i u) i]
  simp only [Matrix.updateRow_self, permanentalCofactor_updateRow]

theorem permanent_updateRow_add (A : Matrix ι ι ℝ) (i : ι) (u v : ι → ℝ) :
    (A.updateRow i (u+v)).permanent =
      (A.updateRow i u).permanent+(A.updateRow i v).permanent := by
  simp only [permanent_updateRow_expansion, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem permanent_updateCol_add (A : Matrix ι ι ℝ) (j : ι) (u v : ι → ℝ) :
    (A.updateCol j (u+v)).permanent =
      (A.updateCol j u).permanent+(A.updateCol j v).permanent := by
  simp only [permanent_updateCol_expansion, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem permanentalCofactor_transpose (A : Matrix ι ι ℝ) (i j : ι) :
    permanentalCofactor A.transpose j i = permanentalCofactor A i j := by
  let u : ι → ℝ := Pi.single j 1
  have h := Matrix.permanent_transpose (A.updateRow i u)
  rw [← Matrix.updateCol_transpose, permanent_updateCol_expansion,
    permanent_updateRow_expansion] at h
  simpa [u, Pi.single_apply, ite_mul] using h

end
end DittertRybin
