import DR.Endpoint.TwoZeroCompetitor
import DR.Endpoint.PermanentSupportBlocks

/-! Every actual minimum on the two-independent-zero face has strictly
expanding support, hence all its permanental cofactors are positive. -/

namespace DittertRybin

def twoZeroAllowed (n : ℕ) (i j : Fin (n+2)) : Prop :=
  ¬(i = 0 ∧ j = 1) ∧ ¬(i = 1 ∧ j = 0)

theorem twoZeroCompetitor_on_face (n : ℕ) :
    ∀ i j, ¬twoZeroAllowed n i j → twoZeroCompetitor n i j = 0 := by
  intro i j h
  unfold twoZeroAllowed at h
  have hz : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by tauto
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact (twoZeroCompetitor_zeros n).1
  · exact (twoZeroCompetitor_zeros n).2

theorem PermanentFaceMinimum.twoZero_permanent_lt_two {n : ℕ} (hn : 0 < n)
    {A : Board (n+2) (n+2)} (hmin : PermanentFaceMinimum (twoZeroAllowed n) A) :
    A.permanent < 2*dittertConstant (n+2) :=
  (hmin.2.2 _ (twoZeroCompetitor_mem_doublyStochastic n)
    (twoZeroCompetitor_on_face n)).trans_lt (twoZeroCompetitor_permanent_lt_two hn)

theorem PermanentFaceMinimum.twoZero_strictHall {n : ℕ} (hn : 0 < n)
    {A : Board (n+2) (n+2)} (hmin : PermanentFaceMinimum (twoZeroAllowed n) A) :
    StrictPermanentHall A :=
  strictPermanentHall_of_permanent_lt_two hmin.1 (hmin.twoZero_permanent_lt_two hn)

theorem PermanentFaceMinimum.twoZero_cofactor_pos {n : ℕ} (hn : 0 < n)
    {A : Board (n+2) (n+2)} (hmin : PermanentFaceMinimum (twoZeroAllowed n) A)
    (i j : Fin (n+2)) : 0 < permanentalCofactor A i j :=
  (hmin.twoZero_strictHall hn).cofactor_pos
    (fun _ _ => nonneg_of_mem_doublyStochastic hmin.1) i j

/-- The zero-cofactor alternative has now been discharged on this actual face. -/
theorem PermanentFaceMinimum.twoZero_allowed_cofactor_ge {n : ℕ} (hn : 0 < n)
    {A : Board (n+2) (n+2)} (hmin : PermanentFaceMinimum (twoZeroAllowed n) A)
    (i j : Fin (n+2)) (hallowed : twoZeroAllowed n i j) :
    A.permanent ≤ permanentalCofactor A i j :=
  hmin.allowed_cofactor_ge_of_pos i j hallowed (hmin.twoZero_cofactor_pos hn i j)

end DittertRybin
