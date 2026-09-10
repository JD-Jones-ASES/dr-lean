import DR.Endpoint.CutDeficit
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- A positive gcd-grid cut attains 2/(4*6); replacing 2 by 3 is false.
example : (Nat.gcd 4 6 : ℝ)/(4*6) ≤ (3:ℝ)/4 + 2/6 - 1 :=
  positive_rectangular_cut_grid_gcd (by decide) (by decide) (by norm_num)

example : ¬(3:ℝ)/(4*6) ≤ (3:ℝ)/4 + 2/6 - 1 := by norm_num

-- Zero demand cannot be substituted for the strict-positive premise.
example : (2:ℝ)/4 + 3/6 - 1 = 0 ∧
    ¬(Nat.gcd 4 6 : ℝ)/(4*6) ≤ (2:ℝ)/4 + 3/6 - 1 := by norm_num

example : (1:ℝ)/(5*6) ≤ (1:ℝ)/5 + 5/6 - 1 := by
  simpa only [Nat.cast_ofNat, Nat.cast_one] using positive_rectangular_cut_grid_one (m := 5) (n := 6) (k := 1) (l := 5)
    (by decide) (by decide) (by norm_num)

private noncomputable def perturbedDiagonal : Board 2 2 := fun i j =>
  if i.val = j.val then (if i.val=0 then 9/16 else 7/16) else 0

private theorem perturbed_probability : IsProbability perturbedDiagonal := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [perturbedDiagonal]
  · norm_num [totalMass,rowSum,perturbedDiagonal,Fin.sum_univ_succ]

-- The discrepancy is checked for every subset, including empty/full subsets.
private theorem perturbed_discrepancy (I J : Finset (Fin 2)) :
    |(∑ i ∈ I, rowSum perturbedDiagonal i)-(I.card : ℝ)/2| +
    |(∑ j ∈ J, colSum perturbedDiagonal j)-(J.card : ℝ)/2| ≤
      (1/4 : ℝ)*(Nat.gcd 2 2 : ℝ)/(2*2) := by
  fin_cases I <;> fin_cases J <;>
    norm_num [rowSum,colSum,perturbedDiagonal,Fin.sum_univ_succ]

-- The hypothesis can hold at exact equality with positive discrepancy.
example : |rowSum perturbedDiagonal 0-1/2| + |colSum perturbedDiagonal 0-1/2| =
    (1/4 : ℝ)*(Nat.gcd 2 2 : ℝ)/(2*2) := by
  norm_num [rowSum,colSum,perturbedDiagonal,Fin.sum_univ_succ]

-- Construct a balanced matrix from the discrepancy, preserving a boundary zero.
example : ∃ B : Board 2 2, IsProbability B ∧
    (∀ i, rowSum B i = 1/2) ∧ (∀ j, colSum B j = 1/2) ∧
    (∀ i j, (3/4)*B i j ≤ perturbedDiagonal i j) ∧ B 0 1 = 0 := by
  obtain ⟨B,hB,hr,hc,hdom⟩ := exists_balanced_dominated_of_subset_discrepancy_gcd
    (by decide) (by decide) perturbed_probability (by norm_num : (0:ℝ) ≤ 1/4)
    (by norm_num : (1/4:ℝ)<1) perturbed_discrepancy
  refine ⟨B,hB,hr,hc,?_,?_⟩
  · norm_num at hdom ⊢
    exact hdom
  · exact scaled_balanced_zero_of_zero hB.1 (by norm_num : (1/4:ℝ)<1)
      hdom 0 1 (by norm_num [perturbedDiagonal])

-- Actual scaled capacities obey positive, zero and negative cuts together.
example : RectangularTransportCuts ((4/3 : ℝ) • perturbedDiagonal) := by
  have h := rectangularTransportCuts_of_subset_discrepancy (by decide) (by decide)
    (Nat.gcd_dvd_left 2 2) (Nat.gcd_dvd_right 2 2) perturbed_probability
    (by norm_num : (0:ℝ) ≤ 1/4) (by norm_num : (1/4:ℝ)<1) perturbed_discrepancy
  norm_num at h ⊢
  exact h

-- Scaling t=0 is admitted; balanced boundary matrices need not be uniform.
private noncomputable def balancedDiagonal : Board 2 2 := fun i j =>
  if i.val=j.val then 1/2 else 0

private theorem balanced_probability : IsProbability balancedDiagonal := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [balancedDiagonal]
  · norm_num [totalMass,rowSum,balancedDiagonal,Fin.sum_univ_succ]

example : ∃ B : Board 2 2, IsProbability B ∧
    (∀ i, rowSum B i = 1/2) ∧ (∀ j, colSum B j = 1/2) ∧
    ∀ i j, B i j ≤ balancedDiagonal i j := by
  have hdev : ∀ I J : Finset (Fin 2),
      |(∑ i ∈ I, rowSum balancedDiagonal i)-(I.card : ℝ)/2| +
      |(∑ j ∈ J, colSum balancedDiagonal j)-(J.card : ℝ)/2| ≤ (0:ℝ)/(2*2) := by
    intro I J
    have hr (i : Fin 2) : rowSum balancedDiagonal i = 1/2 := by
      fin_cases i <;> norm_num [rowSum,balancedDiagonal,Fin.sum_univ_succ]
    have hc (j : Fin 2) : colSum balancedDiagonal j = 1/2 := by
      fin_cases j <;> norm_num [colSum,balancedDiagonal,Fin.sum_univ_succ]
    simp [hr,hc,div_eq_mul_inv]
  simpa using exists_balanced_dominated_of_subset_discrepancy_one (by decide) (by decide)
    balanced_probability (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)<1) hdev

-- At t=1 the raw scaled-cut inequality is valid, but division and zero
-- inheritance cannot follow: zero scaling dominates a positive matrix.
example : (∀ i j, (1-(1:ℝ))*uniformBoard 2 2 i j ≤ balancedDiagonal i j) ∧
    balancedDiagonal 0 1 = 0 ∧ uniformBoard 2 2 0 1 ≠ 0 := by
  refine ⟨?_,by norm_num [balancedDiagonal],by norm_num [uniformBoard]⟩
  intro i j
  simpa using balanced_probability.1 i j

-- The complementary identity retains signed weights and its correction term.
example : cutMass (fun _ _ => (-1:ℝ) : Board 2 2) {0} {0} = -1 ∧
    cutMass (fun _ _ => (-1:ℝ) : Board 2 2) {0}ᶜ {0}ᶜ = -1 := by
  norm_num [cutMass,Fin.sum_univ_succ,Finset.compl_singleton]

example (P : Board 2 3) : cutMass P {0} {0} =
    rowSum P 0 + colSum P 0-totalMass P+cutMass P {0}ᶜ {0}ᶜ := by
  simpa using cutMass_eq_marginal_deficit_add_complement P {0} {0}

#print axioms positive_rectangular_cut_grid
#print axioms positive_rectangular_cut_grid_one
#print axioms positive_rectangular_cut_grid_gcd
#print axioms cutMass_eq_marginal_deficit_add_complement
#print axioms cutMass_lower_of_subset_discrepancy
#print axioms scaled_cut_demand_le_of_subset_discrepancy
#print axioms cutMass_smul
#print axioms rectangularTransportCuts_of_subset_discrepancy
#print axioms exists_balanced_dominated_of_subset_discrepancy
#print axioms exists_balanced_dominated_of_subset_discrepancy_one
#print axioms exists_balanced_dominated_of_subset_discrepancy_gcd
#print axioms scaled_balanced_zero_of_zero
end DittertRybin.Tests
