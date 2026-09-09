import DR.Square.CapacityDescent
import DR.Square.PermanentCoefficient

/-!
# The homogeneous capacity bound and van der Waerden's inequality

Iterating the proved dimension reduction gives the exact `n! / n^n` bound
for the squarefree coefficient. The matrix product has capacity one and its
squarefree coefficient is the permanent. Equality classification is separate.
-/

open scoped BigOperators
open Finset Set Matrix

namespace DittertRybin

theorem squarefreeExponent_cons (n : ℕ) :
    (squarefreeExponent n).cons 1 = squarefreeExponent (n + 1) := by
  ext j
  cases j using Fin.cases <;> simp [squarefreeExponent_apply]

theorem capacityReduce_squarefree_coefficient {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ) :
    (capacityReduce p).coeff (squarefreeExponent n) = p.coeff (squarefreeExponent (n + 1)) := by
  rw [capacityReduce_coeff, squarefreeExponent_cons]

private theorem homogeneous_fin_one_monomial {p : MvPolynomial (Fin 1) ℝ}
    (hp : p.IsHomogeneous 1) :
    p = MvPolynomial.monomial (squarefreeExponent 1) (p.coeff (squarefreeExponent 1)) := by
  apply MvPolynomial.eq_monomial_of_support_subset_singleton
  intro m hm
  have hsum := hp.degree_eq_sum_deg_support hm
  have hfull : ∑ j ∈ m.support, m j = ∑ j : Fin 1, m j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hnot
    exact Finsupp.notMem_support_iff.mp hnot
  rw [hfull, Fin.sum_univ_one] at hsum
  apply Finsupp.ext
  intro j
  have hj : j = 0 := Subsingleton.elim _ _
  simpa [hj, squarefreeExponent_apply] using hsum.symm

private theorem capacity_le_squarefree_zero {p : MvPolynomial (Fin 0) ℝ}
    (hc : HasNonnegativeCoefficients p) :
    multivariateCapacity (fun x => p.eval x) ≤ p.coeff (squarefreeExponent 0) := by
  have h := multivariateCapacity_le
    (fun x hx => mvPolynomial_eval_nonneg hc (fun j => (hx j).le))
    (x := fun _ => 1) (fun _ => by norm_num)
  have hx : (fun _ : Fin 0 => (1 : ℝ)) = fun _ => 0 := Subsingleton.elim _ _
  have he : squarefreeExponent 0 = 0 := Subsingleton.elim _ _
  simpa [hx, he, MvPolynomial.eval_zero', MvPolynomial.constantCoeff] using h

private theorem capacity_le_squarefree_one {p : MvPolynomial (Fin 1) ℝ}
    (hhom : p.IsHomogeneous 1) (hc : HasNonnegativeCoefficients p) :
    multivariateCapacity (fun x => p.eval x) ≤ p.coeff (squarefreeExponent 1) := by
  have h := multivariateCapacity_le
    (fun x hx => mvPolynomial_eval_nonneg hc (fun j => (hx j).le))
    (x := fun _ => 1) (fun _ => by norm_num)
  have he : p.eval (fun _ => 1) = p.coeff (squarefreeExponent 1) := by
    nth_rw 1 [homogeneous_fin_one_monomial hhom]
    simp [MvPolynomial.eval_monomial]
  simpa [he] using h

theorem dittertConstant_mul_capacityFactor (n : ℕ) :
    dittertConstant n * capacityFactor (n + 1) = dittertConstant (n + 1) := by
  rw [← prod_capacityFactor n, ← Finset.prod_range_succ, prod_capacityFactor]

/-- Gurvits's exact coefficient bound, including zero capacity and n=0,1. -/
theorem homogeneous_capacity_bound {n : ℕ} {p : MvPolynomial (Fin n) ℝ}
    (hhom : p.IsHomogeneous n) (hc : HasNonnegativeCoefficients p)
    (hp : p = 0 ∨ HStable p) :
    dittertConstant n * multivariateCapacity (fun x => p.eval x) ≤
      p.coeff (squarefreeExponent n) := by
  induction n with
  | zero => simpa [dittertConstant] using capacity_le_squarefree_zero hc
  | succ n ih =>
    cases n with
    | zero => simpa [dittertConstant] using capacity_le_squarefree_one hhom hc
    | succ n =>
      have hredHom := capacityReduce_isHomogeneous hhom
      have hredC := capacityReduce_nonnegative hc
      have hredS := capacityReduce_zero_or_hStable hhom hc hp
      have hred := ih hredHom hredC hredS
      rw [capacityReduce_squarefree_coefficient] at hred
      have hstep := capacityReduce_capacity_lower_bound hhom hc hp (by omega)
      have hnonneg : 0 ≤ dittertConstant (n + 1) := by unfold dittertConstant; positivity
      calc
        dittertConstant (n + 1 + 1) * multivariateCapacity (fun x => p.eval x) =
            dittertConstant (n + 1) *
              (capacityFactor (n + 1 + 1) * multivariateCapacity (fun x => p.eval x)) := by
                rw [← dittertConstant_mul_capacityFactor]
                ring
        _ ≤ dittertConstant (n + 1) * multivariateCapacity (fun x => (capacityReduce p).eval x) :=
          mul_le_mul_of_nonneg_left hstep hnonneg
        _ ≤ _ := hred

/-- The exact van der Waerden permanent lower bound, with no stability or
capacity premise on the input matrix. -/
theorem permanent_lower_bound_of_doublyStochastic {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) : dittertConstant n ≤ A.permanent := by
  have h := homogeneous_capacity_bound (matrixProductPolynomial_isHomogeneous A)
    (matrixProductPolynomial_nonnegative (fun i j => nonneg_of_mem_doublyStochastic hA))
    (Or.inr (matrixProductPolynomial_hStable_of_doublyStochastic hA))
  rw [matrixProductPolynomial_squarefree_coefficient] at h
  simpa [matrixProductPolynomial_capacity_eq_one hA] using h

end DittertRybin
