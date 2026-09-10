import DR.Square.ZeroRectangle
import DR.Square.OrderThree

namespace DittertRybin.Tests
open scoped BigOperators
open Matrix

-- The prescribed zero is away from the first row and first column. All
-- labels must therefore pass through the actual permutation equivalence.
private noncomputable def sharpZeroThree : Board 3 3 := fun i j =>
  if i.val=2 then (if j.val=1 then 0 else 1/2)
    else if j.val=1 then 1/2 else 1/4

private theorem sharpZeroThree_ds : sharpZeroThree ∈ doublyStochastic ℝ (Fin 3) := by
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨?_,?_,?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [sharpZeroThree]
  · intro i
    fin_cases i <;> norm_num [sharpZeroThree,Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [sharpZeroThree,Fin.sum_univ_succ]

example : (1/4 : ℝ) ≤ sharpZeroThree.permanent := by
  have h := permanent_lower_bound_of_zero_rectangle sharpZeroThree_ds {2} {1}
    (by norm_num) (by
      intro i hi j hj
      simp only [Finset.mem_singleton] at hi hj
      subst i; subst j
      norm_num [sharpZeroThree])
  norm_num [dittertConstant,Nat.factorial] at h ⊢
  exact h

-- The exact lower constant is attained; a larger face floor is false.
example : sharpZeroThree.permanent = (1/4 : ℝ) ∧ ¬(1/3 : ℝ) ≤ sharpZeroThree.permanent := by
  rw [permanent_three]
  norm_num [sharpZeroThree]

private def sharpZeroFourRational : Matrix (Fin 4) (Fin 4) ℚ := fun i j =>
  if i.val=0 then (if j.val=0 then 0 else 1/3)
    else if j.val=0 then 1/3 else 2/9

private noncomputable def sharpZeroFour : Board 4 4 :=
  fun i j => (sharpZeroFourRational i j : ℝ)

private theorem sharpZeroFour_ds : sharpZeroFour ∈ doublyStochastic ℝ (Fin 4) := by
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨?_,?_,?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [sharpZeroFour,sharpZeroFourRational]
  · intro i
    fin_cases i <;> norm_num [sharpZeroFour,sharpZeroFourRational,Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [sharpZeroFour,sharpZeroFourRational,Fin.sum_univ_succ]

-- Here gamma_(n-r-s)=gamma_2 is nontrivial. The actual sharp matrix detects
-- an erroneously squared denominator in the claimed factorial ratio.
example : sharpZeroFour ∈ doublyStochastic ℝ (Fin 4) ∧
    sharpZeroFour.permanent = dittertConstant 3*dittertConstant 3/dittertConstant 2 ∧
    ¬dittertConstant 3*dittertConstant 3/(dittertConstant 2)^2 ≤ sharpZeroFour.permanent := by
  have hq : sharpZeroFourRational.permanent = (8/81 : ℚ) := by decide +kernel
  have hmap : (sharpZeroFourRational.permanent : ℝ) = sharpZeroFour.permanent := by
    simp only [Matrix.permanent,Rat.cast_sum,Rat.cast_prod,sharpZeroFour]
  have hv : sharpZeroFour.permanent = (8/81 : ℝ) := by
    rw [← hmap,hq]
    norm_num
  exact ⟨sharpZeroFour_ds,by norm_num [hv,dittertConstant,Nat.factorial],
    by norm_num [hv,dittertConstant,Nat.factorial]⟩

-- An empty forbidden axis gives precisely the van der Waerden constant.
example : dittertConstant 3 ≤ sharpZeroThree.permanent := by
  have h := permanent_lower_bound_of_zero_rectangle sharpZeroThree_ds ∅ {1}
    (by norm_num) (by simp)
  norm_num [dittertConstant,Nat.factorial] at h ⊢
  exact h

-- Additional zero entries are allowed: a permutation matrix lies on the
-- same face, including a two-row by one-column prescribed rectangle.
example : (1/9 : ℝ) ≤ (1 : Board 4 4).permanent := by
  have hds : (1 : Board 4 4) ∈ doublyStochastic ℝ (Fin 4) := by
    exact (doublyStochastic ℝ (Fin 4)).one_mem
  have hz : ∀ i∈({0,1} : Finset (Fin 4)), ∀ j∈({3} : Finset (Fin 4)),
      (1 : Board 4 4) i j=0 := by
    intro i hi j hj
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
    subst j
    rcases hi with rfl | rfl <;> norm_num [Matrix.one_apply] <;> decide
  have h := permanent_lower_bound_of_zero_rectangle hds {0,1} {3} (by norm_num) hz
  norm_num [dittertConstant,Nat.factorial] at h ⊢

-- Without the actual zero-rectangle premise, the strengthened bound fails
-- even on a doubly stochastic matrix.
example : ¬(1/4 : ℝ) ≤ (uniformDittertMatrix 3).permanent := by
  rw [permanent_three]
  norm_num [uniformDittertMatrix]

-- The total degree across both selected variables is essential: each of
-- two separate exponent-one bounds does not give total degree one.
example : ¬HasSubsetDegreeBound
    (MvPolynomial.X (0 : Fin 2)*MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ)
    (prefixVariables 2 2) 1 := by
  intro h
  have hm : Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1 ∈
      (MvPolynomial.X (0 : Fin 2)*MvPolynomial.X 1 : MvPolynomial (Fin 2) ℝ).support := by
    rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul]
    simp
  have hb := h _ hm
  norm_num [prefixVariables,Finset.sum_filter,Fin.sum_univ_succ,Finsupp.single_apply] at hb

-- The genuine coefficient-one deletion consumes one unit, independently
-- of signs and independently of stability.
example {p : MvPolynomial (Fin 5) ℝ}
    (hp : HasSubsetDegreeBound p (prefixVariables 5 3) 4) :
    HasSubsetDegreeBound (capacityReduce p) (prefixVariables 4 2) 3 :=
  hp.capacityReduce

example : (∑ j∈prefixVariables 4 3,
    (Finsupp.single (1 : Fin 3) 2).cons 1 j) = 3 := by
  rw [sum_prefixVariables_cons]
  norm_num [prefixVariables,Fin.sum_univ_succ,Finsupp.single_apply]

-- The support-degree bridge itself does not assume nonnegative entries.
example : HasSubsetDegreeBound
    (matrixProductPolynomial (!![0,-1;-2,-3] : Board 2 2)) {0} 1 := by
  have h := matrixProductPolynomial_subset_degree (!![0,-1;-2,-3] : Board 2 2) {0} {0}
    (by intro i hi j hj; simp only [Finset.mem_singleton] at hi hj; subst i; subst j; rfl)
  simpa using h

-- Zero polynomial and zero capacity do not require a positivity workaround.
example : dittertConstant 2*dittertConstant 2/dittertConstant 1 *
    multivariateCapacity (fun x => (0 : MvPolynomial (Fin 3) ℝ).eval x) ≤
      (0 : MvPolynomial (Fin 3) ℝ).coeff (squarefreeExponent 3) :=
  subset_degree_capacity_bound (n := 2) (s := 1) (d := 1) (by decide)
    (MvPolynomial.isHomogeneous_zero _ _ _) (by intro e; simp) (Or.inl rfl)
    (hasSubsetDegreeBound_zero _ _)

-- The ratio retains the empty selected prefix and a positive residual degree.
example : dittertConstant 3 * (∏ j∈Finset.range 0, capacityFactor (3+j+1)) =
    dittertConstant 3 := by simp

example : dittertConstant 1 * (∏ j∈Finset.range 2, capacityFactor (1+j+1)) =
    dittertConstant 3 := prod_shifted_capacityFactor 1 2

#print axioms matrixProductPolynomial_subset_degree
#print axioms HasSubsetDegreeBound.capacityReduce
#print axioms singleVariableSlice_natDegree_le_coordinate
#print axioms capacityReduce_capacity_lower_bound_of_coordinate
#print axioms subset_degree_capacity_bound_product
#print axioms prod_shifted_capacityFactor
#print axioms subset_degree_capacity_bound
#print axioms permanent_lower_bound_of_zero_prefix
#print axioms zeroRectanglePrefixEquiv_mem
#print axioms permanent_lower_bound_of_zero_rectangle
end DittertRybin.Tests
