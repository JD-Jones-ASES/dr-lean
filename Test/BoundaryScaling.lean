import DR.Endpoint.Arithmetic

namespace DittertRybin.Tests

-- The exact square-completion argument includes a zero rook deficit.
example : ¬((1-(0 : ℝ))^3*(1/100)*2 ≤ 1/100-0) := by
  intro h
  exact endpoint_boundary_scaling_contradiction (m := 3) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h

-- A positive deficit has its exact square-root scaling coordinate.
example : ¬((1-(1/100 : ℝ))^3*(1/100)*2 ≤ 1/100-1/10000) := by
  intro h
  exact endpoint_boundary_scaling_contradiction (m := 3) (L := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h

-- Strictness of the scalar gap is indispensable: equality permits equality
-- in the Bernoulli boundary comparison at t=1.
example : (1 : ℝ)^2*1*1/4 = (2-1)/2^2 ∧
    (1-(1 : ℝ))^1*1*2 ≤ 1-1 := by norm_num

example : let L : ℝ := (2*3*18^2/(3*3^2))*(1+(18-1)*(1/10^12)/(1/10^12))
    (1/10^12 : ℝ) < 1/4 ∧ 0 < L ∧ L*(1/10^12) < 1 ∧
      3^2*(1/10^12)*L/4 < (16/17 : ℝ)^2/(3*(18-1)^2) :=
  endpoint_scaling_parameter_bounds (M := 3) (N := 18) (G := 3)
    (a := 1/10^12) (b := 1/10^12) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- The common divisor's upper bound cannot be discarded in the scalar lemma.
example : (1 : ℝ)+(18-1)*1 < (512/289)*1000000^2/(3^3*18^2*(18-1)^2) ∧
    ¬(1 : ℝ) < 1/4 := by norm_num

private theorem arithmetic_cut_256_300 :
    (22 : ℝ)*300*Real.log 256 ≤ (256 : ℝ)*(256-1) := by
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have he : Real.log (256 : ℝ) = 8*Real.log 2 := by
    rw [show (256 : ℝ) = 2^8 by norm_num, Real.log_pow]
    norm_num
  rw [he]
  linarith

-- A genuinely rectangular admitted instance, in both orientations.
example : UniformMaximizer 256 300 256 ∧ UniformMaximizer 300 256 256 :=
  uniform_maximum_arithmetic_endpoint (by decide) (by decide) arithmetic_cut_256_300

-- Exact real quotient form and full closed-simplex equality interface.
example {m n : ℕ} (hm : 128 ≤ m) (hmn : m ≤ n)
    (hcut : (n : ℝ) ≤ (m : ℝ)*(m-1)/(22*Real.log (m : ℝ)))
    (P : Board m n) (hP : ∀ i j, 0 ≤ P i j) (hs : totalMass P = 1) :
    separationProbability P m ≤ uniformSeparationValue m n m ∧
    (separationProbability P m = uniformSeparationValue m n m ↔ P = uniformBoard m n) :=
  (uniform_maximum_arithmetic_endpoint_of_le hm hmn hcut).1 P ⟨hP, hs⟩

-- A supplied zero is handled by the actual boundary exclusion, not by
-- an interior-only maximizer statement or an assumed permanent floor.
example {m n g : ℕ} (hm : 3 ≤ m) (hn : 18 ≤ n) (hmn : m ≤ n) (hg : 1 ≤ g)
    (hgm : g ∣ m) (hgn : g ∣ n)
    (hc : distinctUniformProbability n m+((n : ℝ)-1)*dittertConstant m <
      (512/289)*(g : ℝ)^2/((m : ℝ)^3*(n : ℝ)^2*((n : ℝ)-1)^2))
    (P : Board m n) (hP : IsProbability P) (i : Fin m) (j : Fin n) (hz : P i j = 0) :
    separationProbability P m < uniformSeparationValue m n m := by
  by_contra h
  exact endpoint_boundary_contender_impossible_of_arithmetic hm hn hmn hg hgm hgn hc
    hP (le_of_not_gt h) ⟨i,j,hz⟩

#print axioms endpoint_boundary_scaling_contradiction
#print axioms endpoint_scaling_parameter_bounds
#print axioms endpoint_boundary_contender_impossible_of_arithmetic
#print axioms uniform_maximum_endpoint_of_arithmetic_criterion
#print axioms uniform_maximum_endpoint_of_boundary_criterion
#print axioms uniform_maximum_arithmetic_endpoint
#print axioms uniform_maximum_arithmetic_endpoint_of_le
end DittertRybin.Tests
