import DR.Endpoint.TwoZeroFaceSupport

namespace DittertRybin
open scoped BigOperators

example : (twoZeroCompetitor 0).permanent = 1 := by
  norm_num [twoZeroCompetitor_permanent, Nat.factorial]

example : (twoZeroCompetitor 0).permanent = 2*dittertConstant 2 := by
  norm_num [twoZeroCompetitor_permanent, dittertConstant, Nat.factorial]

example : (twoZeroCompetitor 1).permanent = 8/27 := by
  norm_num [twoZeroCompetitor_permanent, Nat.factorial]

example : (twoZeroCompetitor 2).permanent = 7/64 := by
  norm_num [twoZeroCompetitor_permanent, Nat.factorial]

example (n : ℕ) : twoZeroCompetitor n ∈ doublyStochastic ℝ (Fin (n+2)) ∧
    twoZeroCompetitor n 0 1 = 0 ∧ twoZeroCompetitor n 1 0 = 0 :=
  ⟨twoZeroCompetitor_mem_doublyStochastic n, twoZeroCompetitor_zeros n⟩

example : ¬StrictPermanentHall (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  have ht := h {0} (by simp) (by decide)
  norm_num [permanentSupportNeighbors, Finset.filter_insert, Finset.filter_singleton,
    Matrix.one_apply, show (Finset.univ : Finset (Fin 2)) = {0,1} by decide] at ht

/-- With no constant rows, the signed formula is precisely the two-by-two permanent. -/
example (a b c d : ℝ) :
    Matrix.permanent (!![a,b;c,d]) = a*d+b*c := by
  have h := permanent_two_exceptional_rows (n := 0) (!![a,b;c,d]) (-2)
    (fun i => Fin.elim0 i)
  norm_num [Fin.sum_univ_succ] at h
  nlinarith

/-- A negative constant remainder is included in the algebraic identity. -/
example : Matrix.permanent (fun _ _ : Fin 3 => (-2 : ℝ)) = -48 := by
  norm_num [permanent_const, Nat.factorial]

example {n : ℕ} {A : Board n n} (hA : A ∈ doublyStochastic ℝ (Fin n))
    (hsmall : A.permanent < 2*dittertConstant n) (i j : Fin n) :
    0 < permanentalCofactor A i j :=
  (strictPermanentHall_of_permanent_lt_two hA hsmall).cofactor_pos
    (fun _ _ => nonneg_of_mem_doublyStochastic hA) i j

/-- The face minimum is taken over every matrix on the closed face. -/
example {n : ℕ} (hn : 0 < n) (A : Board (n+2) (n+2))
    (hDS : A ∈ doublyStochastic ℝ (Fin (n+2)))
    (hzero : ∀ i j, ¬twoZeroAllowed n i j → A i j = 0)
    (hmin : ∀ B : Board (n+2) (n+2), B ∈ doublyStochastic ℝ (Fin (n+2)) →
      (∀ i j, ¬twoZeroAllowed n i j → B i j = 0) → A.permanent ≤ B.permanent)
    (i j : Fin (n+2)) : 0 < permanentalCofactor A i j :=
  PermanentFaceMinimum.twoZero_cofactor_pos hn ⟨hDS,hzero,hmin⟩ i j

#print axioms permanent_one_exceptional_row
#print axioms permanent_two_exceptional_rows
#print axioms twoZeroCompetitor_mem_doublyStochastic
#print axioms twoZeroCompetitor_permanent_ratio
#print axioms twoZeroCompetitor_permanent_lt_two
#print axioms StrictPermanentHall.forced_matching
#print axioms StrictPermanentHall.cofactor_pos
#print axioms permanent_lower_bound_of_tight_support
#print axioms strictPermanentHall_of_permanent_lt_two
#print axioms PermanentFaceMinimum.twoZero_cofactor_pos
#print axioms PermanentFaceMinimum.twoZero_allowed_cofactor_ge

end DittertRybin
