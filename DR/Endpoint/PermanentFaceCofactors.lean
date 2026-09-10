import DR.Square.Permanent
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! Permanental cofactors, Euler identities, and the derivative of the actual
permanent along a signed matrix direction. These are finite polynomial
identities and do not assume minimizer structure. -/

namespace DittertRybin
open scoped BigOperators

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cofactor as a sum over full permutations with one fixed matched cell.
The chosen column factor is omitted, so the definition is independent of that entry. -/
noncomputable def permanentalCofactor (A : Matrix ι ι ℝ) (i j : ι) : ℝ :=
  ∑ σ : Equiv.Perm ι, if σ j = i then ∏ k ∈ Finset.univ.erase j, A (σ k) k else 0

theorem permanentalCofactor_nonneg {A : Matrix ι ι ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (i j : ι) : 0 ≤ permanentalCofactor A i j := by
  unfold permanentalCofactor
  apply Finset.sum_nonneg
  intro σ _
  split_ifs
  · exact Finset.prod_nonneg fun k _ => hA (σ k) k
  · norm_num

theorem permanentalCofactor_contraction (A E : Matrix ι ι ℝ) :
    (∑ i, ∑ j, E i j*permanentalCofactor A i j) =
      ∑ σ : Equiv.Perm ι, ∑ j, E (σ j) j*∏ k ∈ Finset.univ.erase j, A (σ k) k := by
  simp only [permanentalCofactor, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ j, ∑ i, ∑ σ : Equiv.Perm ι,
      E i j*(if σ j = i then ∏ k ∈ Finset.univ.erase j, A (σ k) k else 0)) =
      ∑ j, ∑ σ : Equiv.Perm ι, E (σ j) j*∏ k ∈ Finset.univ.erase j, A (σ k) k := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_comm]
        simp [mul_ite]
    _ = _ := Finset.sum_comm

theorem permanentalCofactor_column_euler (A : Matrix ι ι ℝ) (j : ι) :
    (∑ i, A i j*permanentalCofactor A i j) = A.permanent := by
  simp only [permanentalCofactor, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  apply Finset.sum_congr rfl
  intro σ _
  exact Finset.mul_prod_erase Finset.univ (fun k => A (σ k) k) (Finset.mem_univ j)

theorem permanentalCofactor_row_euler (A : Matrix ι ι ℝ) (i : ι) :
    (∑ j, A i j*permanentalCofactor A i j) = A.permanent := by
  simp only [permanentalCofactor, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  have heach (j : ι) : A i j*(if σ j = i then
      ∏ k ∈ Finset.univ.erase j, A (σ k) k else 0) =
      if j = σ.symm i then ∏ k, A (σ k) k else 0 := by
    by_cases h : σ j = i
    · have hj : j = σ.symm i := by simpa using congrArg σ.symm h
      simp only [hj, if_true]
      simpa using Finset.mul_prod_erase (Finset.univ) (fun k => A (σ k) k)
        (Finset.mem_univ (σ.symm i))
    · have hj : j ≠ σ.symm i := by intro hj; apply h; simp [hj]
      simp [h, hj]
  simp only [heach, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem hasDerivAt_permanent_line (A E : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => Matrix.permanent (fun i j => A i j+t*E i j))
      (∑ i, ∑ j, E i j*permanentalCofactor A i j) 0 := by
  rw [permanentalCofactor_contraction]
  have h : HasDerivAt (fun t : ℝ => ∑ σ : Equiv.Perm ι,
      ∏ j, (A (σ j) j+t*E (σ j) j))
      (∑ σ : Equiv.Perm ι, ∑ j,
        (∏ k ∈ Finset.univ.erase j, (A (σ k) k+(0 : ℝ)*E (σ k) k))*E (σ j) j) 0 := by
    apply HasDerivAt.fun_sum
    intro σ _
    simpa only [smul_eq_mul, one_mul, id_eq] using HasDerivAt.fun_finsetProd (u := Finset.univ)
      (fun j _ => ((hasDerivAt_id (0 : ℝ)).mul_const (E (σ j) j)).const_add (A (σ j) j))
  simpa only [Matrix.permanent, zero_mul, add_zero, mul_comm] using h

end
end DittertRybin
