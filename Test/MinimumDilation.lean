import DR.Endpoint.MinimumDilation

namespace DittertRybin.Tests
open scoped BigOperators

private noncomputable def dilationBalanced : Board 3 3 := fun i j =>
  if i = 0 then (if j = 0 then 0 else 1/6)
    else if j = 0 then 1/6 else 1/12

private noncomputable def dilationPositive : Board 3 3 := fun i j =>
  (7/8 : ℝ)*dilationBalanced i j + if i = 0 ∧ j = 0 then 1/8 else 0

private theorem dilationBalanced_probability : IsProbability dilationBalanced := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [dilationBalanced]
  · norm_num [totalMass, rowSum, dilationBalanced, Fin.sum_univ_succ]

private theorem dilationBalanced_rows (i : Fin 3) :
    rowSum dilationBalanced i = 1/(3 : ℝ) := by
  fin_cases i <;> norm_num [rowSum, dilationBalanced, Fin.sum_univ_succ]

private theorem dilationBalanced_cols (j : Fin 3) :
    colSum dilationBalanced j = 1/(3 : ℝ) := by
  fin_cases j <;> norm_num [colSum, dilationBalanced, Fin.sum_univ_succ]

private theorem dilationPositive_probability : IsProbability dilationPositive := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [dilationPositive, dilationBalanced]
  · norm_num [totalMass, rowSum, dilationPositive, dilationBalanced, Fin.sum_univ_succ]

private theorem dilationPositive_domination (i j : Fin 3) :
    (7/8 : ℝ)*dilationBalanced i j ≤ dilationPositive i j := by
  fin_cases i <;> fin_cases j <;> norm_num [dilationPositive, dilationBalanced]

private theorem dilationPositive_active :
    cutMass dilationPositive {1,2} {1,2} =
      (7/8 : ℝ)*rectangularCutDemand ({1,2} : Finset (Fin 3)) ({1,2} : Finset (Fin 3)) := by
  simp only [cutMass, Finset.sum_insert (by decide : (1 : Fin 3) ∉ ({2} : Finset (Fin 3))), Finset.sum_singleton]
  norm_num [rectangularCutDemand, dilationPositive, dilationBalanced, show ({1,2} : Finset (Fin 3)).card = 2 from by decide, show (2 : Fin 3) ≠ 0 from by decide]

-- The active balanced zero is new: the original board is strictly positive.
example : (∀ i j, 0 < dilationPositive i j) ∧ dilationBalanced 0 0 = 0 := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [dilationPositive, dilationBalanced]
  · norm_num [dilationBalanced]

example : cutMass dilationBalanced ({1,2} : Finset (Fin 3))ᶜ {1,2}ᶜ = 0 :=
  active_dilation_cut_complement_zero (by norm_num : (0 : ℝ)<7/8)
    dilationBalanced_probability dilationBalanced_rows dilationBalanced_cols
    dilationPositive_domination {1,2} {1,2} dilationPositive_active

-- The physical active cut bounds every competing balanced dilation.
example {C : Board 3 3} {u : ℝ} (hu : 0 ≤ u) (hC : IsProbability C)
    (hr : ∀ i, rowSum C i = 1/(3 : ℝ)) (hc : ∀ j, colSum C j = 1/(3 : ℝ))
    (hdom : ∀ i j, u*C i j ≤ dilationPositive i j) : u ≤ (7/8 : ℝ) :=
  rectangular_dilation_le_active hu hC hr hc hdom {1,2} {1,2}
    (by norm_num [rectangularCutDemand, show ({1,2} : Finset (Fin 3)).card = 2 from by decide, show (2 : Fin 3) ≠ 0 from by decide]) dilationPositive_active

-- Here every positive cut has positive mass. The finite minimization
-- constructs a genuine balanced board, including all omitted nonpositive cuts.
example : ∃ (q : ℝ) (B : Board 3 3) (I J : Finset (Fin 3)),
    0 < q ∧ q ≤ 1 ∧ IsProbability B ∧
    (∀ i, rowSum B i = 1/(3 : ℝ)) ∧ (∀ j, colSum B j = 1/(3 : ℝ)) ∧
    (∀ i j, q*B i j ≤ dilationPositive i j) ∧ 0 < rectangularCutDemand I J ∧
    cutMass dilationPositive I J = q*rectangularCutDemand I J ∧
    cutMass B Iᶜ Jᶜ = 0 := by
  apply exists_minimum_rectangular_dilation (by decide) (by decide) dilationPositive_probability
  intro I J
  fin_cases I <;> fin_cases J <;>
    norm_num [rectangularCutDemand, cutMass, dilationPositive, dilationBalanced]

-- A whole cut attains unit demand, while one empty axis cannot be positive.
example : rectangularCutDemand (Finset.univ : Finset (Fin 3))
    (Finset.univ : Finset (Fin 5)) = 1 :=
  rectangularCutDemand_univ (by decide) (by decide)

example : rectangularCutDemand (∅ : Finset (Fin 3))
    (Finset.univ : Finset (Fin 5)) = 0 := by
  norm_num [rectangularCutDemand]

-- Unit domination at equal total mass forces equality, even with zeros.
example {P : Board 3 3} (hP : IsProbability P)
    (hdom : ∀ i j, dilationBalanced i j ≤ P i j) : P = dilationBalanced :=
  probability_eq_of_entrywise_le hP dilationBalanced_probability hdom

-- A zero original row precludes every positive balanced dilation. This
-- detects removal of the positive-cut-mass hypothesis from existence.
example {B : Board 2 2} {q : ℝ} (hq : 0 < q) (hB : IsProbability B)
    (hr : ∀ i, rowSum B i = 1/(2 : ℝ))
    (hdom : ∀ i j, q*B i j ≤ if i = 0 ∧ j = 0 then (1 : ℝ) else 0) : False := by
  have h0 := hdom 1 0
  have h1 := hdom 1 1
  norm_num at h0 h1
  have hz0 : B 1 0 = 0 := le_antisymm (by nlinarith only [h0, hq]) (hB.1 _ _)
  have hz1 : B 1 1 = 0 := le_antisymm (by nlinarith only [h1, hq]) (hB.1 _ _)
  have hh := hr 1
  norm_num [rowSum, Fin.sum_univ_succ, hz0, hz1] at hh

#print axioms rectangularCutDemand_univ
#print axioms balanced_cut_complement_identity
#print axioms active_dilation_cut_complement_zero
#print axioms exists_minimum_rectangular_dilation
#print axioms rectangular_dilation_le_active
#print axioms probability_eq_of_entrywise_le

end DittertRybin.Tests
