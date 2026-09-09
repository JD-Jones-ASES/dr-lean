import DR.Certificates.WeightedPair

namespace DittertRybin.Certificates.Tests
open scoped BigOperators

-- The empty and signed boundaries are part of the exact homogeneous identity.
example (p : Fin 0 → ℝ) : (∑ a,∑ b,unorderedPairWeight a b*p a*p b)=0 := by simp
example : (∑ a : Fin 2,∑ b : Fin 2,unorderedPairWeight a b*
    (if a.val=0 then 2 else -1)*(if b.val=0 then 2 else -1))=3 := by
  have h := sum_unorderedPairWeight (fun a : Fin 2 => if a.val=0 then (2:ℝ) else -1)
  norm_num [Fin.sum_univ_two] at h ⊢
  exact h

-- Two equal positive masses give 3/4, retaining the diagonal multiplier correction.
example : (∑ a : Fin 2,∑ b : Fin 2,unorderedPairWeight a b*(1/2)*(1/2))=(3/4:ℝ) := by
  have h := sum_unorderedPairWeight (fun _ : Fin 2 => (1/2:ℝ))
  norm_num at h ⊢
  exact h

example {α : Type*} [Fintype α] [DecidableEq α] (p : α → ℝ) (hp : ∀ a,0≤p a)
    (hmass : ∑ a,p a=1) (Q : α → α → Matrix α α ℝ) (x : α → ℝ)
    (c E : ℝ) (hc : 0≤c) (hE : 0≤E) (hQ : ∀ a b,c*E≤quadraticValue (Q a b) x) :
    (c/2)*E≤∑ a,∑ b,unorderedPairWeight a b*p a*p b*quadraticValue (Q a b) x :=
  weightedPair_quadratic_lower p hp hmass Q x c E hc hE hQ

#print axioms sum_unorderedPairWeight
#print axioms weightedPair_quadratic_lower
end DittertRybin.Certificates.Tests
