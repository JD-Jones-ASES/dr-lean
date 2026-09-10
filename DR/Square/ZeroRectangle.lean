import DR.Square.ZeroRectangleCapacity
import DR.Square.BlockFloor

/-! A prescribed zero rectangle sharpens van der Waerden's bound. The proof
uses the actual row-product polynomial and restricted-degree capacity descent,
then transports arbitrary row/column labels by an explicit finite equivalence.
No minimizer classification or cofactor theorem is assumed. -/
namespace DittertRybin
open scoped BigOperators
open Matrix

/-- A zero rectangle whose columns are the first s coordinates. Empty forbidden
row/column sets are admitted; the remaining degree must be positive. -/
theorem permanent_lower_bound_of_zero_prefix {n s : ℕ} {A : Board (n+s) (n+s)}
    (hA : A ∈ doublyStochastic ℝ (Fin (n+s))) (I : Finset (Fin (n+s)))
    (hI : I.card<n)
    (hz : ∀ i∈I, ∀ j∈prefixVariables (n+s) s, A i j=0) :
    dittertConstant n * dittertConstant (n+s-I.card) / dittertConstant (n-I.card) ≤
      A.permanent := by
  have hD := matrixProductPolynomial_subset_degree A I (prefixVariables (n+s) s) hz
  have hdim : n+s-I.card = (n-I.card)+s := by omega
  rw [hdim] at hD ⊢
  have h := subset_degree_capacity_bound (n := n) (s := s) (d := n-I.card)
    (by omega) (matrixProductPolynomial_isHomogeneous A)
    (matrixProductPolynomial_nonnegative (fun i j => nonneg_of_mem_doublyStochastic hA))
    (Or.inr (matrixProductPolynomial_hStable_of_doublyStochastic hA)) hD
  rw [matrixProductPolynomial_squarefree_coefficient,matrixProductPolynomial_capacity_eq_one hA,
    mul_one] at h
  exact h

/-- Reorder all labels so a given subset occupies exactly the first coordinates. -/
noncomputable def zeroRectanglePrefixEquiv {n : ℕ} (J : Finset (Fin n)) :
    Fin (n-J.card+J.card) ≃ Fin n :=
  (finCongr (Nat.add_comm (n-J.card) J.card)).trans
    (finSumFinEquiv.symm.trans
      (((Fintype.equivFinOfCardEq (by simp : Fintype.card J=J.card)).symm.sumCongr
        (Fintype.equivFinOfCardEq (by simp : Fintype.card ↥(Jᶜ)=n-J.card)).symm).trans
        (finsetSumCompl J)))

theorem zeroRectanglePrefixEquiv_mem {n : ℕ} (J : Finset (Fin n))
    (j : Fin (n-J.card+J.card)) (hj : j∈prefixVariables (n-J.card+J.card) J.card) :
    zeroRectanglePrefixEquiv J j ∈ J := by
  have hlt : j.val<J.card := by simpa [prefixVariables] using hj
  have he : finCongr (Nat.add_comm (n-J.card) J.card) j =
      Fin.castAdd (n-J.card) ⟨j.val,hlt⟩ := rfl
  unfold zeroRectanglePrefixEquiv
  simp only [Equiv.trans_apply,he,finSumFinEquiv_symm_apply_castAdd,Equiv.sumCongr_apply,
    Sum.map_inl]
  exact ((Fintype.equivFinOfCardEq (by simp : Fintype.card J=J.card)).symm ⟨j.val,hlt⟩).property

/-- Sharp forbidden-rectangle lower bound on the whole doubly stochastic face,
including all additional zeros and arbitrary physical row/column subsets. -/
theorem permanent_lower_bound_of_zero_rectangle {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (I J : Finset (Fin n))
    (hsize : I.card+J.card<n) (hz : ∀ i∈I, ∀ j∈J, A i j=0) :
    dittertConstant (n-I.card)*dittertConstant (n-J.card)/dittertConstant (n-I.card-J.card) ≤
      A.permanent := by
  let e := zeroRectanglePrefixEquiv J
  let I' := I.map e.symm.toEmbedding
  have hIcard : I'.card=I.card := Finset.card_map _
  have hB : A.submatrix e e ∈ doublyStochastic ℝ (Fin (n-J.card+J.card)) :=
    reindex_mem_doublyStochastic (e₁ := e.symm) (e₂ := e.symm) hA
  have hz' : ∀ i∈I', ∀ j∈prefixVariables (n-J.card+J.card) J.card,
      (A.submatrix e e) i j=0 := by
    intro i hi j hj
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hi
    simpa only [Matrix.submatrix_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using
      hz a ha (e j) (zeroRectanglePrefixEquiv_mem J j hj)
  have h := permanent_lower_bound_of_zero_prefix hB I' (by omega) hz'
  rw [permanent_submatrix_equiv,hIcard] at h
  have hjle : J.card≤n := by simpa using Finset.card_le_univ (s := J)
  have hdim : n-J.card+J.card=n := Nat.sub_add_cancel hjle
  have hsub : n-J.card-I.card=n-I.card-J.card := by omega
  rw [hdim,hsub] at h
  simpa only [mul_comm] using h

end DittertRybin
