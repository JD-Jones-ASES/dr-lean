import DR.Endpoint.NearEndpointPadding
import DR.Endpoint.NearEndpointMarginals
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators

-- Each deleted index is an actual physical position, even at the edge.
example : deletedIndexOrderEmbeddingEquiv 3 (1 : Fin 4) (0 : Fin 3) = 0 ∧
    deletedIndexOrderEmbeddingEquiv 3 (1 : Fin 4) (1 : Fin 3) = 2 := by decide

-- The zero-draw minor of a one-cell core is the empty permanent1.
private theorem empty_rook (P : Board 1 1) : rookSum P 0 = 1 := by
  have hc : Fintype.card (Fin 0 ↪o Fin 1) = 1 :=
    (Fintype.card_congr (deletedIndexOrderEmbeddingEquiv 0)).symm
  simp [rookSum,hc]
example (P : Board 1 1) : rookSum P 0 = 1 := empty_rook P

example (P : Board 1 1) : (cornerZeroBorder P 0 2 (-3)).permanent = -6 := by
  rw [permanent_cornerZeroBorder]
  rw [empty_rook]
  norm_num

-- Signed bordering preserves the sign and both independent border factors.
private theorem signed_border :
    (cornerZeroBorder (fun _ _ : Fin 2 => (-1 : ℝ)) (-2) 3 (-5)).permanent = -120 := by
  have h := permanent_cornerZeroBorder (fun _ _ : Fin 2 => (-1 : ℝ)) (-2) 3 (-5)
  have hc := rookSum_const 2 2 1 (-1)
  norm_num at hc
  rw [hc] at h
  norm_num at h
  exact h
example : (cornerZeroBorder (fun _ _ : Fin 2 => (-1 : ℝ)) (-2) 3 (-5)).permanent = -120 :=
  signed_border

-- At degree2, an extra sample factorial would incorrectly double the answer.
private theorem border_three :
    (cornerZeroBorder (fun _ _ : Fin 3 => (1 : ℝ)) 2 3 5).permanent = 1080 := by
  have h := permanent_cornerZeroBorder (fun _ _ : Fin 3 => (1 : ℝ)) 2 3 5
  have hc := rookSum_const 3 3 2 1
  norm_num at hc
  rw [hc] at h
  norm_num at h
  exact h
example : (cornerZeroBorder (fun _ _ : Fin 3 => (1 : ℝ)) 2 3 5).permanent ≠ 2160 := by
  rw [border_three]
  norm_num

-- The uniform padded reference is μ4=8/81, not gamma4=3/32.
private theorem uniform_padding_three :
    (nearEndpointPadding (uniformBoard 3 3)).permanent = 8/81 := by
  rw [permanent_nearEndpointPadding_uniform (by decide)]
  norm_num [boundaryPermanentFloor]
example : (nearEndpointPadding (uniformBoard 3 3)).permanent = 8/81 := uniform_padding_three
example : (nearEndpointPadding (uniformBoard 3 3)).permanent ≠ dittertConstant 4 := by
  rw [uniform_padding_three]
  norm_num [dittertConstant]

example : nearEndpointRookRatio (uniformBoard 3 3) = 2/3 := by
  rw [nearEndpointRookRatio_uniform (by decide)]
  norm_num [distinctUniformProbability, Nat.descFactorial]

example : nearEndpointRookDeficit (uniformBoard 3 3) = 0 := by
  simp [nearEndpointRookDeficit, nearEndpointRookRatio_uniform (by decide : 0 < 3)]

private noncomputable def balancedBoundary : Board 2 2 :=
  fun i j => if i=j then 1/2 else 0

private theorem balancedBoundary_probability : IsProbability balancedBoundary := by
  constructor
  · intro i j; unfold balancedBoundary; split_ifs <;> norm_num
  · norm_num [totalMass,rowSum,balancedBoundary,Fin.sum_univ_succ]

-- Actual boundary zeros survive in rows and columns distinct from the dummy corner.
example : ∃ i₁ i₂ j₁ j₂ : Fin 3, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
    nearEndpointPadding balancedBoundary i₁ j₁ = 0 ∧
    nearEndpointPadding balancedBoundary i₂ j₂ = 0 := by
  apply nearEndpointPadding_two_independent_zeros
  exact ⟨0,1,by norm_num [balancedBoundary]⟩

example : nearEndpointPadding balancedBoundary ∈ doublyStochastic ℝ (Fin 3) := by
  apply nearEndpointPadding_mem_doublyStochastic (by decide) balancedBoundary_probability.1
  · intro i; fin_cases i <;> norm_num [rowSum,balancedBoundary,Fin.sum_univ_succ]
  · intro j; fin_cases j <;> norm_num [colSum,balancedBoundary,Fin.sum_univ_succ]

-- n=2 has K=1: uniqueness cannot be inferred from any contender argument.
example : separationProbability balancedBoundary (2-1) = 1 ∧
    balancedBoundary ≠ uniformBoard 2 2 := by
  refine ⟨separationProbability_one balancedBoundary_probability,?_⟩
  intro h
  have he := congrArg (fun P : Board 2 2 => P 0 1) h
  norm_num [balancedBoundary,uniformBoard] at he

-- The new border is well-defined even when the original board is empty.
example (P : Board 0 0) : (nearEndpointPadding P).permanent = 0 := by
  exact Matrix.permanent_eq_elem_of_subsingleton _ (0 : Fin 1)

-- The transport scale handles δ=0 and does not assume the balanced board exists.
example {n : ℕ} (hn : 3 ≤ n) {P : Board n n} (hP : IsProbability P)
    (hc : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1))
    (ha : distinctUniformProbability n (n-1) ≤ 1/4)
    (hs : (4/3 : ℝ)*(n : ℝ)^2*distinctUniformProbability n (n-1) < 1) :
    ∃ (t : ℝ) (B : Board n n), 0 ≤ t ∧ t < 1 ∧
      t^2 = (4/3 : ℝ)*(n : ℝ)^2*nearEndpointRookDeficit P ∧ IsProbability B ∧
      (∀ i, rowSum B i = 1/(n : ℝ)) ∧ (∀ j, colSum B j = 1/(n : ℝ)) ∧
      ∀ i j, (1-t)*B i j ≤ P i j :=
  nearEndpoint_contender_exists_balanced_domination hn hP hc ha hs

#print axioms succAboveOrderEmb_bijective
#print axioms rookSum_pred_eq_sum_permanent_minors
#print axioms permanent_cornerZeroBorder
#print axioms permanent_nearEndpointPadding
#print axioms nearEndpointPadding_two_independent_zeros
#print axioms nearEndpointPadding_mem_doublyStochastic
#print axioms permanent_nearEndpointPadding_eq_ratio
#print axioms nearEndpoint_contender_deficit_budget
#print axioms nearEndpoint_contender_subset_discrepancy_sq
#print axioms nearEndpoint_contender_exists_balanced_domination
end DittertRybin.Tests
