import DR.Square.ZeroRectangleDegree

/-! Capacity descent with the degree in the selected variables, rather than
the full homogeneous degree. This is the sharp loss needed for a forbidden
rectangle. Zero polynomials and capacity zero remain in every step. -/
namespace DittertRybin
open scoped BigOperators

/-- A single variable's exponent bound controls every real specialization. -/
theorem singleVariableSlice_natDegree_le_coordinate {σ : Type*} [DecidableEq σ]
    {p : MvPolynomial σ ℝ} (i : σ) (x : σ → ℝ) {d : ℕ}
    (h : ∀ e∈p.support, e i≤d) : (singleVariableSlice p i x).natDegree ≤ d := by
  unfold singleVariableSlice
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ j∈e.support, if j=i then e j else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hj : j=i
      · subst j
        simp
      · simp [hj]
    _ ≤ e i := by
      simp only [Finset.sum_ite_eq',Finsupp.mem_support_iff]
      split_ifs <;> omega
    _ ≤ d := h e he

/-- One-variable degree can be strictly smaller than total homogeneous degree. -/
theorem capacityReduce_capacity_lower_bound_of_coordinate {n h d : ℕ}
    {p : MvPolynomial (Fin (n+1)) ℝ} (hhom : p.IsHomogeneous h)
    (hc : HasNonnegativeCoefficients p) (hp : p=0 ∨ HStable p) (hd : 2≤d)
    (hdegree : ∀ e∈p.support, e 0≤d) :
    capacityFactor d * multivariateCapacity (fun x => p.eval x) ≤
      multivariateCapacity (fun x => (capacityReduce p).eval x) := by
  apply le_multivariateCapacity
  intro x hx
  have hxcons : ∀ j : Fin (n+1), 0 < (Fin.cons 1 x : Fin (n+1) → ℝ) j := by
    intro j
    cases j using Fin.cases
    · norm_num
    · exact hx _
  have hslice := polynomial_capacity_le_deriv
    (singleVariableSlice_splits_of_zero_or_hStable hhom hp 0 hxcons)
    (singleVariableSlice_coeff_nonneg hc 0 (fun j => (hxcons j).le)) hd
    (singleVariableSlice_natDegree_le_coordinate 0 (Fin.cons 1 x) hdegree)
  rw [← capacityReduce_eval] at hslice
  have hcap := mul_le_mul_of_nonneg_left
    (multivariateCapacity_mul_prod_le_slice_capacity hc hx) (capacityFactor_pos hd).le
  rw [le_div_iff₀ (Finset.prod_pos fun j _ => hx j)]
  calc
    capacityFactor d * multivariateCapacity (fun y => p.eval y) * ∏ j, x j =
        capacityFactor d * (multivariateCapacity (fun y => p.eval y) * ∏ j, x j) := by ring
    _ ≤ _ := hcap.trans hslice

/-- The zero-th coordinate lies in every nonempty prefix. -/
theorem HasSubsetDegreeBound.zero_coordinate {n s d : ℕ}
    {p : MvPolynomial (Fin (n+1)) ℝ}
    (hp : HasSubsetDegreeBound p (prefixVariables (n+1) (s+1)) d) :
    ∀ e∈p.support, e 0≤d := by
  intro e he
  apply (Finset.single_le_sum (f := fun i => e i) (fun i _ => Nat.zero_le _) ?_).trans (hp e he)
  simp [prefixVariables]

/-- Delete s selected coordinates with the successive restricted-degree losses,
then apply the ordinary homogeneous bound on the remaining n variables. -/
theorem subset_degree_capacity_bound_product {n s d : ℕ} (hd : 1≤d)
    {p : MvPolynomial (Fin (n+s)) ℝ} (hhom : p.IsHomogeneous (n+s))
    (hc : HasNonnegativeCoefficients p) (hp : p=0 ∨ HStable p)
    (hdegree : HasSubsetDegreeBound p (prefixVariables (n+s) s) (d+s)) :
    dittertConstant n * (∏ j∈Finset.range s, capacityFactor (d+j+1)) *
      multivariateCapacity (fun x => p.eval x) ≤ p.coeff (squarefreeExponent (n+s)) := by
  induction s with
  | zero => simpa using homogeneous_capacity_bound hhom hc hp
  | succ s ih =>
    have hredHom := capacityReduce_isHomogeneous hhom
    have hredC := capacityReduce_nonnegative hc
    have hredS := capacityReduce_zero_or_hStable hhom hc hp
    have hredD := hdegree.capacityReduce
    have hbound := ih hredHom hredC hredS hredD
    rw [capacityReduce_squarefree_coefficient] at hbound
    have hstep := capacityReduce_capacity_lower_bound_of_coordinate hhom hc hp
      (by omega : 2≤d+s+1) hdegree.zero_coordinate
    have hn : 0≤dittertConstant n := by unfold dittertConstant; positivity
    have hf : 0≤∏ j∈Finset.range s, capacityFactor (d+j+1) := by
      apply Finset.prod_nonneg
      intro j _
      exact (capacityFactor_pos (by omega : 2≤d+j+1)).le
    rw [Finset.prod_range_succ]
    calc
      _ = (dittertConstant n*(∏ j∈Finset.range s, capacityFactor (d+j+1)))*
          (capacityFactor (d+s+1)*multivariateCapacity (fun x => p.eval x)) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left hstep (mul_nonneg hn hf)).trans hbound

/-- The selected losses telescope to a ratio of the exact permanent constants. -/
theorem prod_shifted_capacityFactor (d s : ℕ) :
    dittertConstant d * (∏ j∈Finset.range s, capacityFactor (d+j+1)) =
      dittertConstant (d+s) := by
  rw [← prod_capacityFactor (d+s), Finset.prod_range_add, prod_capacityFactor]

/-- Sharp capacity bound with a prescribed restricted total degree. -/
theorem subset_degree_capacity_bound {n s d : ℕ} (hd : 1≤d)
    {p : MvPolynomial (Fin (n+s)) ℝ} (hhom : p.IsHomogeneous (n+s))
    (hc : HasNonnegativeCoefficients p) (hp : p=0 ∨ HStable p)
    (hdegree : HasSubsetDegreeBound p (prefixVariables (n+s) s) (d+s)) :
    (dittertConstant n * dittertConstant (d+s) / dittertConstant d) *
      multivariateCapacity (fun x => p.eval x) ≤ p.coeff (squarefreeExponent (n+s)) := by
  have hg : (0:ℝ)<dittertConstant d := by
    have hdR : (0:ℝ)<d := by exact_mod_cast (by omega : 0<d)
    unfold dittertConstant
    positivity
  have he : dittertConstant n*dittertConstant (d+s)/dittertConstant d =
      dittertConstant n*(∏ j∈Finset.range s, capacityFactor (d+j+1)) := by
    rw [← prod_shifted_capacityFactor d s]
    field_simp
  rw [he]
  exact subset_degree_capacity_bound_product hd hhom hc hp hdegree

end DittertRybin
