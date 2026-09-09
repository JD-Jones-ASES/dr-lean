import DR.Certificates.FiniteK4Soundness

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- Coincident rows alone are not repeated cells.
example : finiteK4MultiplierWeight ![(0:ℕ),0,0,0,0] ![(0:ℕ),1,2,3,4] = 1 := by decide +kernel
-- Repeated cells are retained, with six rather than one as correction.
example : finiteK4MultiplierWeight ![(9:ℕ),9,9,8,7] ![(3:ℕ),3,3,4,5] = 6 := by decide +kernel
-- The event is inclusive OR: distinct columns suffice after deleting position four.
example : finiteK4DeletedSuccess ![(0:ℕ),0,0,0,0] ![(0:ℕ),1,2,3,0] 4 = 1 := by decide +kernel
-- Deleting another position can leave a repeated column, and then both clauses fail.
example : finiteK4DeletedSuccess ![(0:ℕ),0,0,0,0] ![(0:ℕ),1,2,3,0] 1 = 0 := by decide +kernel

-- The constant single-cell certificate gives the actual odd-degree signed identity.
private theorem singleton_local (s : Fin 5 → Fin 1 × Fin 1) :
    finiteK4TripleValue (fun _ => 1) s = 60 * (1 : ℝ) - 12 * (∑ a : Fin 5,
      (finiteK4DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a : ℝ)) := by
  have hs (i : Fin 5) : s i = (0,0) := Subsingleton.elim _ _
  have hd (a : Fin 5) : finiteK4DeletedSuccess (fun i => (s i).1) (fun i => (s i).2) a = 0 := by
    fin_cases a <;> simp only [finiteK4DeletedSuccess, hs]
    all_goals decide +kernel
  have ho (q : Fin 10) : finiteK4QuintetObservable (fun _ => 1) (s ∘ finiteK4TripleOrder q) = 6 := by
    simp only [finiteK4QuintetObservable, finiteK4MultiplierWeight, Function.comp_apply, hs]
    norm_num
  simp only [finiteK4TripleValue, ho, hd, Nat.cast_zero, Finset.sum_const_zero]
  norm_num

example (P : Board 1 1) :
    totalMass P ^ 5 - totalMass P * separationProbability P 4 =
      ∑ t : Fin 3 → Fin 1 × Fin 1, unorderedTripleWeight t * (∏ i, P (t i).1 (t i).2) *
        quadraticValue (finiteK4Entry (fun _ => 1) t) (fun e => P e.1 e.2) := by
  simpa only [one_mul] using finiteK4_probability_identity_of_local 1 (fun _ => 1) singleton_local P

#print axioms finiteK4TripleOrder_bijective
#print axioms finiteK4QuintetObservable_split
#print axioms sum_finiteK4TripleValue
#print axioms sum_finiteK4DeletedSuccess
#print axioms finiteK4_probability_identity_of_local
#print axioms finiteK4_uniformMaximizer_of_local
end DittertRybin.Tests
