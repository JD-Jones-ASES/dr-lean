import DR.Endpoint.SquareNearEndpoint
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests

-- Every finite certificate and the first analytic dimension has a full theorem.
example : UniformMaximizer 21 21 20 := uniform_maximum_square_near_endpoint (by decide)
example : UniformMaximizer 22 22 21 := uniform_maximum_square_near_endpoint (by decide)
example : UniformMaximizer 23 23 22 := uniform_maximum_square_near_endpoint (by decide)
example : UniformMaximizer 24 24 23 := uniform_maximum_square_near_endpoint (by decide)
example : UniformMaximizer 25 25 24 := uniform_maximum_square_near_endpoint (by decide)
example : UniformMaximizer 26 26 25 := uniform_maximum_square_near_endpoint (by decide)
example : UniformMaximizer 1000 1000 999 := uniform_maximum_square_near_endpoint (by decide)

-- Actual closed-simplex hypotheses, with the sharp value written explicitly.
example {n : ℕ} (hn : 21≤n) (P : Board n n) (hP : ∀i j,0≤P i j)
    (hmass : totalMass P=1) :
    separationProbability P (n-1) ≤ distinctUniformProbability n (n-1)*(2-distinctUniformProbability n (n-1)) ∧
      (separationProbability P (n-1) = distinctUniformProbability n (n-1)*(2-distinctUniformProbability n (n-1)) ↔
        P=uniformBoard n n) := by
  have h := uniform_maximum_square_near_endpoint hn P ⟨hP,hmass⟩
  have hv : uniformSeparationValue n n (n-1) =
      distinctUniformProbability n (n-1)*(2-distinctUniformProbability n (n-1)) := by
    unfold uniformSeparationValue
    ring
  simpa only [hv] using h

-- Transposition retains the same actual-matrix equality domain.
example {n : ℕ} (hn : 21≤n) (P : Board n n) (hP : IsProbability P) :
    separationProbability P.transpose (n-1) ≤ uniformSeparationValue n n (n-1) ∧
      (separationProbability P.transpose (n-1)=uniformSeparationValue n n (n-1) ↔
        P.transpose=uniformBoard n n) :=
  uniform_maximum_square_near_endpoint hn P.transpose hP.transpose

-- A zero anywhere forces a strict gap, including at the first finite dimension.
example (P : Board 21 21) (hP : IsProbability P) (i j : Fin 21) (hz : P i j=0) :
    separationProbability P 20 < uniformSeparationValue 21 21 20 := by
  have h := uniform_maximum_square_near_endpoint (by decide : 21≤21) P hP
  by_contra hnot
  have heq := h.2.mp (le_antisymm h.1 (le_of_not_gt hnot))
  have hcell := congrArg (fun A : Board 21 21 => A i j) heq
  norm_num [uniformBoard,hz] at hcell

-- The uniform probability board realizes the exact equality case.
example {n : ℕ} (hn : 21≤n) :
    separationProbability (uniformBoard n n) (n-1)=uniformSeparationValue n n (n-1) :=
  (uniform_maximum_square_near_endpoint hn _
    (uniformBoard_isProbability (by omega) (by omega))).2.mpr rfl

private noncomputable def nearEndpointConcentratedTwo : Board 2 2 :=
  fun i j => if i.val=0 ∧ j.val=0 then 1 else 0

private theorem nearEndpointConcentratedTwo_probability : IsProbability nearEndpointConcentratedTwo := by
  constructor
  · intro i j
    unfold nearEndpointConcentratedTwo
    split_ifs <;> norm_num
  · unfold totalMass rowSum
    simp only [Fin.sum_univ_succ]
    norm_num [nearEndpointConcentratedTwo]

-- Removing the range guard admits n=2,K=1, where uniform uniqueness is false.
example : ¬UniformMaximizer 2 2 (2-1) := by
  intro h
  have hp := nearEndpointConcentratedTwo_probability
  have hv : separationProbability nearEndpointConcentratedTwo 1=uniformSeparationValue 2 2 1 := by
    rw [separationProbability_one hp]
    norm_num [uniformSeparationValue,distinctUniformProbability,Nat.descFactorial]
  have heq := (h _ hp).2.mp hv
  have hcell := congrArg (fun A : Board 2 2 => A 0 0) heq
  norm_num [nearEndpointConcentratedTwo,uniformBoard] at hcell

#print axioms nearEndpoint_required_permanent_bound
#print axioms uniform_maximum_square_near_endpoint
end DittertRybin.Tests
