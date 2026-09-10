import DR.Endpoint.PermanentSupportHall
import DR.Square.BlockFloor
import DR.Endpoint.GammaBlockGap

/-! Actual doubly stochastic support cuts. A failure of strict Hall produces
a proper diagonal block split and its unconditional permanent floor. -/

namespace DittertRybin
open scoped BigOperators

theorem permanentSupportNeighbors_complement_zero {n : ℕ} {A : Board n n}
    (hA : ∀ i j, 0 ≤ A i j) (S : Finset (Fin n)) :
    cutMass A (permanentSupportNeighbors A S)ᶜ S = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  apply le_antisymm _ (hA i j)
  by_contra h
  have hm : i ∈ permanentSupportNeighbors A S :=
    (mem_permanentSupportNeighbors _ _ _).mpr ⟨j, hj, lt_of_not_ge h⟩
  exact (Finset.mem_compl.mp hi) hm

theorem permanentSupportNeighbors_cutMass {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (S : Finset (Fin n)) :
    cutMass A (permanentSupportNeighbors A S) S = S.card := by
  have h := cutMass_add_compl_rows A (permanentSupportNeighbors A S) S
  rw [permanentSupportNeighbors_complement_zero
    (fun _ _ => nonneg_of_mem_doublyStochastic hA) S, add_zero] at h
  simpa only [colSum, sum_col_of_mem_doublyStochastic hA,
    Finset.sum_const, nsmul_eq_mul, mul_one] using h

theorem permanentSupportNeighbors_card {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (S : Finset (Fin n)) :
    S.card ≤ (permanentSupportNeighbors A S).card := by
  have h := cutMass_add_compl_cols A (permanentSupportNeighbors A S) S
  rw [permanentSupportNeighbors_cutMass hA S] at h
  have hn := cutMass_nonneg (A := A) (fun _ _ => nonneg_of_mem_doublyStochastic hA)
    (permanentSupportNeighbors A S) Sᶜ
  simp only [rowSum, sum_row_of_mem_doublyStochastic hA,
    Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact_mod_cast (show (S.card : ℝ) ≤ (permanentSupportNeighbors A S).card by linarith)

/-- Equality in the ordinary Hall cardinality bound creates a genuine block
decomposition. The resulting floor does not require strict positivity. -/
theorem permanent_lower_bound_of_tight_support {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) (S : Finset (Fin n))
    (hcard : (permanentSupportNeighbors A S).card = S.card) :
    dittertConstant S.card*dittertConstant (n-S.card) ≤ A.permanent := by
  have hz : cutMass A (permanentSupportNeighbors A S) Sᶜ = 0 := by
    have h := cutMass_add_compl_cols A (permanentSupportNeighbors A S) S
    rw [permanentSupportNeighbors_cutMass hA S] at h
    simp only [rowSum, sum_row_of_mem_doublyStochastic hA,
      Finset.sum_const, nsmul_eq_mul, mul_one, hcard] at h
    linarith
  have h := permanent_lower_bound_of_diagonal_block_mass hA
    (permanentSupportNeighbors A S) S hcard 0 (by norm_num) (by norm_num) hz
  simpa [hcard] using h

/-- A permanent strictly below every proper block floor forces strict Hall
support. The hypotheses concern scalar bounds, never an assumed support shape. -/
theorem strictPermanentHall_of_below_block_floors {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hsmall : ∀ k : ℕ, 0 < k → k < n →
      A.permanent < dittertConstant k*dittertConstant (n-k)) :
    StrictPermanentHall A := by
  intro S hS hproper
  have hw := permanentSupportNeighbors_card hA S
  by_contra hs
  have he : (permanentSupportNeighbors A S).card = S.card := by omega
  have hk : 0 < S.card := Finset.card_pos.mpr hS
  have hkn : S.card < n := by
    have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ S, hproper⟩)
    simpa using hlt
  exact (hsmall S.card hk hkn).not_ge (permanent_lower_bound_of_tight_support hA S he)

/-- A quantitative permanent upper bound excludes every proper support split. -/
theorem strictPermanentHall_of_permanent_lt_two {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hsmall : A.permanent < 2*dittertConstant n) : StrictPermanentHall A := by
  apply strictPermanentHall_of_below_block_floors hA
  intro k hk hkn
  have h := dittertConstant_mul_ge_twice (show 1 ≤ k by omega)
    (show 1 ≤ n-k by omega)
  rw [Nat.add_sub_of_le hkn.le] at h
  exact hsmall.trans_le h

end DittertRybin
