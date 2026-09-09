import DR.Certificates.WeightedTriple

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- All three multiplicity cases retain the full unordered multiplier weight.
example : unorderedTripleWeight (fun _ : Fin 3 => (0 : ℕ)) = 1 := by norm_num [unorderedTripleWeight]
example : unorderedTripleWeight (fun i : Fin 3 => if i=2 then (1 : ℕ) else 0) = 1/3 := by norm_num [unorderedTripleWeight, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide]
example : unorderedTripleWeight (fun i : Fin 3 => i) = 1/6 := by norm_num [unorderedTripleWeight, show (0 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 2 by decide]
-- A repeated pair in nonadjacent positions gets the same correction.
example : unorderedTripleWeight (fun i : Fin 3 => if i=1 then (1 : ℕ) else 0) = 1/3 := by norm_num [unorderedTripleWeight]
example : unorderedTripleWeight (fun i : Fin 3 => if i=1 then (1 : ℕ) else 0) ≠ 1/6 := by norm_num [unorderedTripleWeight]

-- A signed single-outcome quintic has odd degree, not the sign of a quartic.
example : (∑ s : Fin 5 → Fin 1, sampleMass (fun _ => (-1 : ℝ)) s *
    (1 : ℝ) * (1 : ℝ)) = -1 := by
  norm_num [sampleMass]

-- The exact product decomposition remains valid when there are no outcomes.
example (w : (Fin 3 → Fin 0) → ℝ) (Q : (Fin 3 → Fin 0) → Matrix (Fin 0) (Fin 0) ℝ) :
    (∑ s : Fin 5 → Fin 0, sampleMass (fun _ => (1 : ℝ)) s *
      w (fun i => s (Fin.castAdd 2 i)) * Q (fun i => s (Fin.castAdd 2 i)) (s 3) (s 4)) = 0 := by
  rw [sum_sample_five_weighted_quadratic]
  simp

-- A normalized boundary law cannot have a constant value across both outcomes.
example (Q : (Fin 3 → Fin 2) → Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : ∀ m, (Q m).PosSemidef)
    (hkernel : ∀ a, quadraticValue (Q (fun _ => a)) ![1,0] = 0 →
      ∃ t : ℝ, ∀ b : Fin 2, (![1,0] b : ℝ) = t) :
    (∑ m : Fin 3 → Fin 2, unorderedTripleWeight m * (∏ i, (![1,0] (m i) : ℝ)) *
      quadraticValue (Q m) ![1,0]) ≠ 0 := by
  intro hz
  obtain ⟨t,ht⟩ := weightedTriple_zero_forces_constant ![1,0]
    (by intro a; fin_cases a <;> norm_num) (by norm_num [Fin.sum_univ_succ]) Q hQ hkernel hz
  have h0 := ht 0
  have h1 := ht 1
  norm_num at h0 h1
  linarith

#print axioms sum_sample_five_weighted_quadratic
#print axioms weightedTriple_zero_forces_constant
end DittertRybin.Tests
