import DR.Endpoint.RowCollisionIncidence

/-! Taking expectations of the exhaustive actual-assignment bound.
Only nonnegative board entries are needed; row normalization is not used.
The pair and deficit-two quantities are participation masses, with each
participating row counted once. -/

namespace DittertRybin
open scoped BigOperators
open Certificates
set_option backward.isDefEq.respectTransparency false

noncomputable def rowDeletionExpectation {m n : ℕ} (X : Board m n) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => ∑ z : Fin m → Fin n, rowAssignmentMass X z*rowDeletionMatrix z i j

noncomputable def rowDoubletonParticipationMass {m n : ℕ} (X : Board m n) (i : Fin m) : ℝ :=
  ∑ z : Fin m → Fin n, rowAssignmentMass X z*rowDoubletonIncidence z i

noncomputable def rowDeficitTwoParticipationMass {m n : ℕ} (X : Board m n) (i : Fin m) : ℝ :=
  ∑ z : Fin m → Fin n, rowAssignmentMass X z*rowDeficitTwoIncidence z i

theorem quadraticValue_rowDeletionExpectation {m n : ℕ} (X : Board m n) (x : Fin m → ℝ) :
    quadraticValue (rowDeletionExpectation X) x=
      ∑ z : Fin m → Fin n, rowAssignmentMass X z*quadraticValue (rowDeletionMatrix z) x := by
  unfold quadraticValue rowDeletionExpectation
  simp only [Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ∑ i,∑ z : Fin m → Fin n,∑ j,x i*(rowAssignmentMass X z*rowDeletionMatrix z i j)*x j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = ∑ z : Fin m → Fin n,∑ i,∑ j,x i*(rowAssignmentMass X z*rowDeletionMatrix z i j)*x j :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Exact interchange of assignment expectation and a rowwise weighted sum. -/
theorem rowAssignment_sum_incidence {m n : ℕ} (X : Board m n)
    (f : (Fin m → Fin n) → Fin m → ℝ) (y : Fin m → ℝ) :
    (∑ z : Fin m → Fin n,rowAssignmentMass X z*(∑ i,f z i*y i))=
      ∑ i,(∑ z : Fin m → Fin n,rowAssignmentMass X z*f z i)*y i := by
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem rowAssignment_injective_indicator {m n : ℕ} (X : Board m n) (a : ℝ) :
    (∑ z : Fin m → Fin n,rowAssignmentMass X z*(if Function.Injective z then a else 0))=
      rowAvoidance X*a := by
  classical
  rw [rowAvoidance_eq_event]
  unfold rowAssignmentEvent
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z hz
  by_cases hi : Function.Injective z <;> simp [hi]

/-- The actual expectation inequality from the localized collision
criterion, valid for arbitrary nonnegative unnormalized row weights. -/
theorem rowDeletion_expectation_lower {m n : ℕ} (X : Board m n)
    (hX : ∀ i j,0≤X i j) (x : Fin m → ℝ) :
    rowAvoidance X*((∑ i,x i^2)-(∑ i,x i)^2)+
      (∑ i,rowDoubletonParticipationMass X i*x i^2)-
      2*(∑ i,x i)*(∑ i,rowDoubletonParticipationMass X i*x i)-
      2*(∑ i,rowDeficitTwoParticipationMass X i*x i^2) ≤
        -quadraticValue (rowDeletionExpectation X) x := by
  classical
  have h := Finset.sum_le_sum (fun z (_ : z∈Finset.univ) =>
    mul_le_mul_of_nonneg_left (rowDeletion_pointwise_lower z x) (rowAssignmentMass_nonneg X hX z))
  have hinj := rowAssignment_injective_indicator X ((∑ i,x i^2)-(∑ i,x i)^2)
  have hu2 := rowAssignment_sum_incidence X (fun z i => rowDoubletonIncidence z i) (fun i => x i^2)
  have hu1 := rowAssignment_sum_incidence X (fun z i => rowDoubletonIncidence z i) x
  have hv2 := rowAssignment_sum_incidence X (fun z i => rowDeficitTwoIncidence z i) (fun i => x i^2)
  change _ = ∑ i,rowDoubletonParticipationMass X i*x i^2 at hu2
  change _ = ∑ i,rowDoubletonParticipationMass X i*x i at hu1
  change _ = ∑ i,rowDeficitTwoParticipationMass X i*x i^2 at hv2
  have huc : (∑ z : Fin m → Fin n,rowAssignmentMass X z*
      (2*(∑ i,x i)*(∑ i,rowDoubletonIncidence z i*x i)))=
      2*(∑ i,x i)*(∑ i,rowDoubletonParticipationMass X i*x i) := by
    rw [← hu1]
    conv_rhs => rw [Finset.mul_sum (a := 2*(∑ i,x i))]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have hvc : (∑ z : Fin m → Fin n,rowAssignmentMass X z*
      (2*(∑ i,rowDeficitTwoIncidence z i*x i^2)))=
      2*(∑ i,rowDeficitTwoParticipationMass X i*x i^2) := by
    rw [← hv2]
    conv_rhs => rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  have hr : (∑ z : Fin m → Fin n,rowAssignmentMass X z*
      (-quadraticValue (rowDeletionMatrix z) x)) = -quadraticValue (rowDeletionExpectation X) x := by
    rw [quadraticValue_rowDeletionExpectation]
    simp only [mul_neg,Finset.sum_neg_distrib]
  simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib] at h
  rw [hinj,hu2,huc,hvc,hr] at h
  exact h

end DittertRybin
