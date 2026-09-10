import DR.Endpoint.RectangularTransport
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

private noncomputable def boundaryCapacity : Board 2 3 := fun i j =>
  if j.val=1 then 1/2 else if (i.val=0 ∧ j.val=2) ∨ (i.val=1 ∧ j.val=0) then 1/3 else 0
private noncomputable def balancedWitness : Board 2 3 := fun i j =>
  if j.val=1 then 1/6 else if (i.val=0 ∧ j.val=2) ∨ (i.val=1 ∧ j.val=0) then 1/3 else 0

private theorem capacity_nonneg : ∀ i j, 0 ≤ boundaryCapacity i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [boundaryCapacity]

private theorem boundary_feasible : IsRectangularTransport boundaryCapacity balancedWitness := by
  refine ⟨?_,?_,?_,?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [balancedWitness]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [balancedWitness,boundaryCapacity]
  · intro i
    fin_cases i <;> norm_num [rowSum,balancedWitness,Fin.sum_univ_succ]
  · intro j
    fin_cases j <;> norm_num [colSum,balancedWitness,Fin.sum_univ_succ]

-- Capacities need not themselves have mass one or balanced marginals.
example : totalMass boundaryCapacity = 5/3 := by
  norm_num [totalMass,rowSum,boundaryCapacity,Fin.sum_univ_succ]

-- A positive-demand cut can be exactly saturated.
example : cutMass boundaryCapacity Finset.univ {0} =
    ((Finset.univ : Finset (Fin 2)).card : ℝ)/2 +
      (({0} : Finset (Fin 3)).card : ℝ)/3 - 1 := by
  norm_num [cutMass,boundaryCapacity,Fin.sum_univ_succ]

-- Zero-demand cuts are included at equality as well.
example : cutMass boundaryCapacity Finset.univ ∅ = 0 ∧
    ((Finset.univ : Finset (Fin 2)).card : ℝ)/2 +
      ((∅ : Finset (Fin 3)).card : ℝ)/3 - 1 = 0 := by
  norm_num [cutMass]

-- A negative-demand cut with zero capacity remains part of the criterion.
example : cutMass boundaryCapacity {0} {0} = 0 ∧
    (({0} : Finset (Fin 2)).card : ℝ)/2 +
      (({0} : Finset (Fin 3)).card : ℝ)/3 - 1 = -1/6 := by
  norm_num [cutMass,boundaryCapacity]

example : ∃ B, IsRectangularTransport boundaryCapacity B ∧ IsProbability B ∧
    ∃ i j, B i j = 0 := by
  obtain ⟨B,hB⟩ := exists_rectangularTransport_of_cuts (by decide) (by decide)
    boundaryCapacity capacity_nonneg (boundary_feasible.cuts (by decide))
  exact ⟨B,hB,hB.isProbability (by decide),hB.hasZero ⟨0,0,by norm_num [boundaryCapacity]⟩⟩

-- The other dimension ordering goes through the actual transpose wrapper.
example : ∃ B, IsRectangularTransport boundaryCapacity.transpose B :=
  exists_rectangularTransport_of_cuts (by decide) (by decide) _
    (fun i j => capacity_nonneg j i) (boundary_feasible.cuts (by decide)).transpose

-- A partial transport does not saturate the dummy rows. Full demand is essential.
example : IsPartialTransport (rectangularCapacityPadding (by decide : 2 ≤ 3) boundaryCapacity)
    (1/2) 0 ∧
      (0 : Board 3 3) (rectangularPaddingRowEquiv (by decide : 2 ≤ 3) (.inr 0)) 0 ≠ 1/6 := by
  exact ⟨zero_isPartialTransport (rectangularCapacityPadding_nonneg _ _ capacity_nonneg)
    (by norm_num), by norm_num⟩

private noncomputable def rowStar : Board 2 3 := fun i _ => if i.val=0 then 1 else 0

-- Sufficient total capacity does not replace all individual cuts.
example : totalMass rowStar = 3 ∧ ¬∃ B, IsRectangularTransport rowStar B := by
  constructor
  · norm_num [totalMass,rowSum,rowStar,Fin.sum_univ_succ]
  · rintro ⟨B,hB⟩
    have hcut := hB.cuts (by decide) {1} Finset.univ
    norm_num [cutMass,rowStar,Fin.sum_univ_succ] at hcut

-- The empty-original-row case shows that m>0 cannot be dropped.
example : RectangularTransportCuts (0 : Board 0 1) ∧
    ¬∃ B, IsRectangularTransport (0 : Board 0 1) B := by
  constructor
  · intro I J
    have hI : I = ∅ := Subsingleton.elim _ _
    have hJ : (J.card : ℝ) ≤ 1 := by
      exact_mod_cast (show J.card ≤ 1 by simpa using Finset.card_le_univ (s := J))
    simp only [hI,Finset.card_empty,Nat.cast_zero,zero_div,cutMass,
      Finset.sum_empty,zero_add]
    linarith
  · rintro ⟨B,hB⟩
    have hc := hB.2.2.2 0
    norm_num [colSum] at hc

-- The empty-column case similarly requires n>0.
example : RectangularTransportCuts (0 : Board 1 0) ∧
    ¬∃ B, IsRectangularTransport (0 : Board 1 0) B := by
  constructor
  · exact (show RectangularTransportCuts (0 : Board 0 1) by
      intro I J
      have hI : I = ∅ := Subsingleton.elim _ _
      have hJ : (J.card : ℝ) ≤ 1 := by
        exact_mod_cast (show J.card ≤ 1 by simpa using Finset.card_le_univ (s := J))
      simp only [hI,Finset.card_empty,Nat.cast_zero,zero_div,cutMass,
        Finset.sum_empty,zero_add]
      linarith).transpose
  · rintro ⟨B,hB⟩
    have hr := hB.2.2.1 0
    norm_num [rowSum] at hr

example (P : Board 2 2) (hP : ∀ i j, 0 ≤ P i j) :
    (∃ B, IsRectangularTransport P B) ↔ TransportCuts P (1/2) :=
  transport_iff_cuts hP (by norm_num)

#print axioms rectangular_cut_sum_split
#print axioms rectangular_cut_card_split
#print axioms cutMass_rectangularCapacityPadding
#print axioms rectangularCapacityPadding_transportCuts
#print axioms rectangular_transport_dummy_saturated
#print axioms exists_rectangularTransport_of_cuts_of_le
#print axioms RectangularTransportCuts.transpose
#print axioms exists_rectangularTransport_of_cuts
#print axioms IsRectangularTransport.cuts
#print axioms rectangularTransport_iff_cuts
#print axioms IsRectangularTransport.isProbability
#print axioms IsRectangularTransport.hasZero
#print axioms exists_balanced_dominated_of_rectangular_cuts
end DittertRybin.Tests
