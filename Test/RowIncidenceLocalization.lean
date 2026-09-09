import DR.Endpoint.RowLocalizedExpectation

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- The first doubleton is the one containing the selected row. The triple
-- is represented by the single increasing pair of its other two rows.
example : (rowPairsOutside (0:Fin 3)).card=1 := by decide +kernel
example : ∃ e∈rowPairsOutside (0:Fin 3), (Finset.univ : Finset (Fin 3))={0,e.val.1,e.val.2} :=
  exists_samplePair_complement_triple Finset.univ (by decide) 0 (Finset.mem_univ _)

-- Reversing an ordered pair is not a second admitted index.
example : ¬((1:Fin 3)<0) := by decide +kernel

-- Distinct canonical pairs cannot represent the same exact doubleton.
example {m n : ℕ} (z : Fin m → Fin n) (e f : SampleIndexPair m) (hne : e≠f)
    (he : RowClassPattern ({e.val.1,e.val.2} : Finset (Fin m)) z) :
    ¬RowClassPattern ({f.val.1,f.val.2} : Finset (Fin m)) z :=
  fun hf => hne (rowDoubletonPattern_pair_unique z e f he hf)

-- Exact pair normalization retains signed boards and zero avoidance.
example (X : Board 3 1) (i : Fin 3) :
    rowDoubletonParticipationMass X i/rowAvoidance X=rowLocalizedDoubletonLoad X i :=
  rowDoubletonParticipationMass_div X i

-- A positive avoidance mass is explicit in the final probability bridge;
-- nonnegative board entries alone suffice for its unnormalized mass bound.
example {m n : ℕ} (X : Board m n) (hX : ∀ i j,0≤X i j) (i : Fin m) :
    rowDeficitTwoParticipationMass X i≤
      (∑ e∈rowPairsOutside i,rowTripletonProbability X i e.val.1 e.val.2)+
      ∑ e∈rowCollisionIncident i,∑ f∈rowPairsDisjoint e,rowTwoDoubletonsProbability X e f :=
  rowDeficitTwoParticipationMass_le_sum X hX i

-- Empty row hosts are retained by the actual lower bound, rather than
-- excluded through an arbitrary positive-dimension premise.
example (X : Board 0 0) (hp : 0<rowAvoidance X) (x : Fin 0 → ℝ) :
    rowAvoidance X*((∑ i,x i^2)-(∑ i,x i)^2+
      (∑ i,rowLocalizedDoubletonLoad X i*x i^2)-
      2*(∑ i,x i)*(∑ i,rowLocalizedDoubletonLoad X i*x i)-
      2*(∑ i,rowLocalizedDeficitTwoLoad X i*x i^2))≤
        -quadraticValue (rowDeletionExpectation X) x :=
  rowDeletion_expectation_lower_localized X (fun i => Fin.elim0 i) hp x

#print axioms samplePair_rows_injective
#print axioms rowDoubletonMember_iff
#print axioms rowDoubletonIncidence_eq_sum
#print axioms rowDoubletonParticipationMass_eq_sum
#print axioms rowDoubletonParticipationMass_div
#print axioms rowDeficitTwoMember_exists
#print axioms rowDeficitTwoIncidence_le_sum
#print axioms rowDeficitTwoParticipationMass_le_sum
#print axioms rowDeficitTwoParticipationMass_div_le
#print axioms rowDeletion_expectation_lower_localized

end DittertRybin.Tests
