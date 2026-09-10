import DR.Endpoint.PermanentFaceCofactors
import Mathlib.Analysis.Convex.DoublyStochasticMatrix
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Supported cofactors of an actual doubly stochastic face minimum.
The variation is zero at every zero entry, so it remains in any prescribed
zero face without requiring positive entries throughout the allowed support. -/

namespace DittertRybin
open scoped BigOperators Topology
open Matrix Filter

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The entire closed face, with additional zeros permitted. -/
def PermanentFaceMinimum (allowed : ι → ι → Prop) (A : Matrix ι ι ℝ) : Prop :=
  A ∈ doublyStochastic ℝ ι ∧ (∀ i j, ¬allowed i j → A i j = 0) ∧
    ∀ B : Matrix ι ι ℝ, B ∈ doublyStochastic ℝ ι →
      (∀ i j, ¬allowed i j → B i j = 0) → A.permanent ≤ B.permanent

noncomputable def permanentCofactorDirection (A : Matrix ι ι ℝ) (i j : ι) : ℝ :=
  A i j*(permanentalCofactor A i j-A.permanent)

theorem permanentCofactorDirection_row_sum {A : Matrix ι ι ℝ}
    (hA : A ∈ doublyStochastic ℝ ι) (i : ι) :
    (∑ j, permanentCofactorDirection A i j) = 0 := by
  simp only [permanentCofactorDirection, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, permanentalCofactor_row_euler,
    sum_row_of_mem_doublyStochastic hA, one_mul, sub_self]

theorem permanentCofactorDirection_column_sum {A : Matrix ι ι ℝ}
    (hA : A ∈ doublyStochastic ℝ ι) (j : ι) :
    (∑ i, permanentCofactorDirection A i j) = 0 := by
  simp only [permanentCofactorDirection, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul, permanentalCofactor_column_euler,
    sum_col_of_mem_doublyStochastic hA, one_mul, sub_self]

theorem PermanentFaceMinimum.cofactorLine_localMin {allowed : ι → ι → Prop}
    {A : Matrix ι ι ℝ} (hmin : PermanentFaceMinimum allowed A) :
    IsLocalMin (fun t : ℝ => Matrix.permanent
      (fun i j => A i j+t*permanentCofactorDirection A i j)) 0 := by
  have hp : ∀ᶠ t : ℝ in 𝓝 0, ∀ i j, 0 < 1+t*(permanentalCofactor A i j-A.permanent) := by
    simp only [Filter.eventually_all]
    intro i j
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) 0).eventually_lt
      (by fun_prop) (by norm_num)
  filter_upwards [hp] with t ht
  have hnonneg (i j : ι) : 0 ≤ A i j+t*permanentCofactorDirection A i j := by
    have h := mul_nonneg (show 0 ≤ A i j from nonneg_of_mem_doublyStochastic hmin.1) (ht i j).le
    dsimp [permanentCofactorDirection]
    nlinarith only [h]
  have hDS : (fun i j => A i j+t*permanentCofactorDirection A i j) ∈ doublyStochastic ℝ ι := by
    apply mem_doublyStochastic_iff_sum.mpr
    refine ⟨hnonneg, ?_, ?_⟩
    · intro i
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        permanentCofactorDirection_row_sum hmin.1, sum_row_of_mem_doublyStochastic hmin.1,
        mul_zero, add_zero]
    · intro j
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
        permanentCofactorDirection_column_sum hmin.1, sum_col_of_mem_doublyStochastic hmin.1,
        mul_zero, add_zero]
  have hface : ∀ i j, ¬allowed i j → A i j+t*permanentCofactorDirection A i j = 0 := by
    intro i j hij
    simp [permanentCofactorDirection, hmin.2.1 i j hij]
  simpa only [zero_mul, add_zero] using hmin.2.2 _ hDS hface

theorem PermanentFaceMinimum.supported_cofactor {allowed : ι → ι → Prop}
    {A : Matrix ι ι ℝ} (hmin : PermanentFaceMinimum allowed A)
    (i j : ι) (hij : 0 < A i j) : permanentalCofactor A i j = A.permanent := by
  have hstat := hmin.cofactorLine_localMin.hasDerivAt_eq_zero
    (hasDerivAt_permanent_line A (permanentCofactorDirection A))
  have hidentity (i : ι) :
      (∑ j, A i j*(permanentalCofactor A i j-A.permanent)^2) =
        ∑ j, permanentCofactorDirection A i j*permanentalCofactor A i j := by
    calc
      _ = (∑ j, permanentCofactorDirection A i j*permanentalCofactor A i j)-
          A.permanent*(∑ j, permanentCofactorDirection A i j) := by
            simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            dsimp [permanentCofactorDirection]
            ring
      _ = _ := by rw [permanentCofactorDirection_row_sum hmin.1, mul_zero, sub_zero]
  have hz : (∑ i, ∑ j, A i j*(permanentalCofactor A i j-A.permanent)^2) = 0 := by
    simpa only [hidentity] using hstat
  have hnonneg (i j : ι) : 0 ≤ A i j*(permanentalCofactor A i j-A.permanent)^2 :=
    mul_nonneg (nonneg_of_mem_doublyStochastic hmin.1) (sq_nonneg _)
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => Finset.sum_nonneg fun j _ => hnonneg i j)).mp hz i (Finset.mem_univ i)
  have hcell := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ Finset.univ) => hnonneg i j)).mp hrow j (Finset.mem_univ j)
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hcell).resolve_left hij.ne'))

end
end DittertRybin
