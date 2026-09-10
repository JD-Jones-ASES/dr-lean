import DR.Square.CapacityEquality

/-! The Knopp--Sinkhorn one-zero permanent floor, derived here from the
proved matrix first-deletion entropy bound and homogeneous capacity bound.
This preserves every doubly stochastic boundary matrix, without a support
classification or a boundary-minimization premise. -/

namespace DittertRybin
open scoped BigOperators
open Matrix

noncomputable def boundaryPermanentFloor (n : ℕ) : ℝ :=
  ((n-2).factorial : ℝ) * (((n : ℝ)-2)/((n : ℝ)-1)^2)^(n-2)

noncomputable def boundaryPermanentRatio (n : ℕ) : ℝ :=
  boundaryPermanentFloor n / dittertConstant n

theorem boundaryPermanentFloor_succ_succ (n : ℕ) :
    boundaryPermanentFloor (n+2) =
      (n.factorial : ℝ) * ((n : ℝ)/((n : ℝ)+1)^2)^n := by
  simp only [boundaryPermanentFloor,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_ofNat]
  congr 2
  ring

theorem boundaryPermanentFloor_eq_capacity (n : ℕ) :
    boundaryPermanentFloor (n+2) = dittertConstant (n+1)*capacityFactor (n+1) := by
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  rw [boundaryPermanentFloor_succ_succ]
  simp only [dittertConstant,capacityFactor,Nat.factorial_succ,Nat.cast_mul,
    Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel]
  simp only [add_sub_cancel_right,div_pow,pow_succ]
  field_simp
  ring_nf
  rw [Nat.mul_comm,pow_mul]
  congr 1
  ring

theorem boundaryPermanentFloor_eq_gamma_ratio (n : ℕ) :
    boundaryPermanentFloor (n+2) = (dittertConstant (n+1))^2/dittertConstant n := by
  have hg : 0 < dittertConstant n := by
    cases n with
    | zero => norm_num [dittertConstant]
    | succ n => unfold dittertConstant; positivity
  rw [boundaryPermanentFloor_eq_capacity]
  apply (eq_div_iff hg.ne').mpr
  calc
    dittertConstant (n+1)*capacityFactor (n+1)*dittertConstant n =
        dittertConstant (n+1)*(dittertConstant n*capacityFactor (n+1)) := by ring
    _ = (dittertConstant (n+1))^2 := by rw [dittertConstant_mul_capacityFactor]; ring

theorem boundaryPermanentFloor_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < boundaryPermanentFloor n := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  unfold boundaryPermanentFloor
  apply mul_pos
  · exact_mod_cast Nat.factorial_pos (n-2)
  · apply pow_pos
    apply div_pos (by linarith)
    exact sq_pos_of_pos (by linarith)

theorem permanent_first_column_entropy_lower_bound {n : ℕ}
    {A : Board (n+1) (n+1)} (hA : A ∈ doublyStochastic ℝ (Fin (n+1))) :
    dittertConstant n * matrixEntropyFactor (fun i => A i 0) ≤ A.permanent := by
  have hhom := matrixProductPolynomial_isHomogeneous A
  have hc := matrixProductPolynomial_nonnegative
    (fun i j => nonneg_of_mem_doublyStochastic hA (i := i) (j := j))
  have hs : matrixProductPolynomial A = 0 ∨ HStable (matrixProductPolynomial A) :=
    Or.inr (matrixProductPolynomial_hStable_of_doublyStochastic hA)
  have h := homogeneous_capacity_bound (capacityReduce_isHomogeneous hhom)
    (capacityReduce_nonnegative hc) (capacityReduce_zero_or_hStable hhom hc hs)
  rw [capacityReduce_squarefree_coefficient,matrixProductPolynomial_squarefree_coefficient] at h
  have hg : 0 ≤ dittertConstant n := by unfold dittertConstant; positivity
  apply (mul_le_mul_of_nonneg_left (matrixProduct_first_deletion_capacity hA) hg).trans h

theorem permanent_boundary_lower_bound_zero_zero {n : ℕ} (hn : 1 ≤ n)
    {A : Board (n+2) (n+2)} (hA : A ∈ doublyStochastic ℝ (Fin (n+2)))
    (hz : A 0 0 = 0) : boundaryPermanentFloor (n+2) ≤ A.permanent := by
  have hsum : (∑ i : Fin (n+1), A i.succ 0) = 1 := by
    have h := sum_col_of_mem_doublyStochastic hA 0
    rw [Fin.sum_univ_succ,hz,zero_add] at h
    exact h
  have he := matrixEntropyFactor_lower_bound (by omega : 2 ≤ n+1)
    (fun i : Fin (n+1) => A i.succ 0)
    (fun _ => nonneg_of_mem_doublyStochastic hA) hsum
  have he' : capacityFactor (n+1) ≤ matrixEntropyFactor (fun i => A i 0) := by
    simpa [matrixEntropyFactor,Fin.prod_univ_succ,hz] using he
  rw [boundaryPermanentFloor_eq_capacity]
  have hg : 0 ≤ dittertConstant (n+1) := by unfold dittertConstant; positivity
  exact (mul_le_mul_of_nonneg_left he' hg).trans (permanent_first_column_entropy_lower_bound hA)

/-- The sharp one-zero boundary floor holds for every doubly stochastic matrix.
The n=3 boundary is included in addition to the n>3 source statement. -/
theorem permanent_boundary_lower_bound {n : ℕ} (hn : 3 ≤ n)
    {A : Board n n} (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hz : ∃ i j, A i j = 0) : boundaryPermanentFloor n ≤ A.permanent := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show 2 ≤ n by omega)
  rw [Nat.add_comm] at hk
  subst n
  obtain ⟨i,j,hz⟩ := hz
  let e : Equiv.Perm (Fin (k+2)) := Equiv.swap 0 i
  let f : Equiv.Perm (Fin (k+2)) := Equiv.swap 0 j
  let B := A.submatrix e f
  have hB : B ∈ doublyStochastic ℝ (Fin (k+2)) := by
    apply mem_doublyStochastic_iff_sum.mpr
    refine ⟨fun _ _ => nonneg_of_mem_doublyStochastic hA,?_,?_⟩
    · intro r
      change ∑ c, A (e r) (f c) = 1
      rw [Equiv.sum_comp f,sum_row_of_mem_doublyStochastic hA]
    · intro c
      change ∑ r, A (e r) (f c) = 1
      exact (Equiv.sum_comp e (fun r => A r (f c))).trans (sum_col_of_mem_doublyStochastic hA (f c))
  have hzero : B 0 0 = 0 := by simpa [B,e,f] using hz
  have hp : B.permanent = A.permanent := by
    change ((A.submatrix id f).submatrix e id).permanent = A.permanent
    rw [Matrix.permanent_permute_cols,Matrix.permanent_permute_rows]
  have h : boundaryPermanentFloor (k+2) ≤ B.permanent :=
    permanent_boundary_lower_bound_zero_zero (by omega) hB hzero
  simpa only [hp] using h

end DittertRybin
