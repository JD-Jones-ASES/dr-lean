import DR.Square.AllOrders
import DR.Rectangular.OrderTwo
import DR.Rectangular.OrderThreeFinal
import DR.Rectangular.FourRowFinal
import DR.Rectangular.FiveByFiveOrderFour
import DR.Rectangular.TwentyByTwentyOrderFour
import DR.Rectangular.LargeBoards
import DR.Endpoint.AllAspects
import DR.Endpoint.Quadratic
import DR.Endpoint.Quartic
import DR.Endpoint.Combined
import DR.Endpoint.Consecutive
import DR.Endpoint.NearSquare
import DR.Endpoint.SquareNearEndpoint
import DR.Endpoint.Arithmetic
import DR.Endpoint.Double
import DR.Endpoint.LLLStrip
import DR.Rectangular.SmallSideFinal
import DR.Rectangular.FiveByFiveFinal

/-!
# Dittert's conjecture and proved ranges of Rybin's semimatching problem

The square theorem is on all nonnegative real matrices of total mass n.
The rectangular statements use ordered independent cell draws with replacement.
Success means distinct rows OR distinct columns, including their intersection.
Every stated maximum includes the full closed simplex and exact uniform equality.
The remaining unrestricted rectangular problem is not claimed here.

This proof draft implements all twenty completed release targets. It does not
import Challenge; all fixed definitions and statement types match it exactly.
-/

open scoped BigOperators

namespace DittertRybinRelease

/-- The entire probability simplex of real m-by-n matrices, allowing zero cells. -/
def IsProbability {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∑ i, ∑ j, P i j) = 1

/-- The probability that k independent draws have distinct rows or distinct columns.
The finite sum ranges over all ordered samples, including repeated cells. -/
noncomputable def separationProbability {m n : ℕ}
    (P : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) : ℝ := by
  classical
  exact ∑ s : Fin k → Fin m × Fin n,
    if Function.Injective (fun t => (s t).1) ∨ Function.Injective (fun t => (s t).2)
    then ∏ t, P (s t).1 (s t).2 else 0

/-- Uniform success a+b-ab, using falling factorials a=(m)_k/m^k and b=(n)_k/n^k. -/
noncomputable def uniformSeparationValue (m n k : ℕ) : ℝ :=
  let a := (m.descFactorial k : ℝ) / (m : ℝ)^k
  let b := (n.descFactorial k : ℝ) / (n : ℝ)^k
  a + b - a*b

/-- The sharp inequality and its unique equality case for every probability matrix.
No positive-entry, balance, or support condition is imposed. -/
def UniformMaximizer (m n k : ℕ) : Prop :=
  ∀ P : Matrix (Fin m) (Fin n) ℝ, IsProbability P →
    separationProbability P k ≤ uniformSeparationValue m n k ∧
    (separationProbability P k = uniformSeparationValue m n k ↔
      P = fun _ _ => ((m : ℝ)*n)⁻¹)

private theorem probability_eq {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℝ) :
    IsProbability P = DittertRybin.IsProbability P := by rfl

private theorem value_eq (m n k : ℕ) :
    uniformSeparationValue m n k = DittertRybin.uniformSeparationValue m n k := by rfl

private theorem separation_eq {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℝ) (k : ℕ) :
    separationProbability P k = DittertRybin.separationProbability P k := by
  classical
  unfold separationProbability DittertRybin.separationProbability DittertRybin.eventMass
    DittertRybin.sampleMass DittertRybin.RowsDistinct DittertRybin.ColsDistinct
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : Function.Injective (fun t => (s t).1) ∨ Function.Injective (fun t => (s t).2)
  · simp [hs]
  · simp [hs]

private theorem maximizer_eq (m n k : ℕ) :
    UniformMaximizer m n k = DittertRybin.UniformMaximizer m n k := by
  unfold UniformMaximizer DittertRybin.UniformMaximizer DittertRybin.uniformBoard
  simp only [probability_eq, separation_eq, value_eq]

/-- Dittert’s sharp inequality and unique equality for every positive order. -/
theorem dittert_unique_maximum {n : ℕ} (hn : 0 < n) :
    ∀ A : Matrix (Fin n) (Fin n) ℝ,
      (∀ i j, 0 ≤ A i j) → (∑ i, ∑ j, A i j) = (n : ℝ) →
      (∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - A.permanent ≤
        2 - (n.factorial : ℝ)/(n : ℝ)^n ∧
      ((∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - A.permanent =
        2 - (n.factorial : ℝ)/(n : ℝ)^n ↔ A = fun _ _ => (n : ℝ)⁻¹) := by
  exact DittertRybin.dittert_unique_maximum hn

/-- Order two on every admissible rectangle. -/
theorem uniform_maximum_order_two {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    UniformMaximizer m n 2 := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_order_two hm hn

/-- Order three on every admissible rectangle. -/
theorem uniform_maximum_order_three {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) :
    UniformMaximizer m n 3 := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_order_three hm hn

/-- Order four on every four-row rectangle, including its transpose. -/
theorem uniform_maximum_four_rows {n : ℕ} (hn : 4 ≤ n) :
    UniformMaximizer 4 n 4 ∧ UniformMaximizer n 4 4 := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_four_rows hn

/-- Order four on the full five-by-five simplex. -/
theorem uniform_maximum_five_by_five_order_four : UniformMaximizer 5 5 4 := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_five_by_five_order_four

/-- Order four on the full twenty-by-twenty simplex. -/
theorem uniform_maximum_twenty_by_twenty_order_four : UniformMaximizer 20 20 4 := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_twenty_by_twenty_order_four

/-- Every order k ≥ 4 above the explicit collision threshold in both dimensions. -/
theorem uniform_maximum_large_boards {m n k : ℕ} (hk : 4 ≤ k)
    (hm : 128*(k-2)*(k.choose 2*((k.choose 2)^2).choose 2 + 1)^2 ≤ m)
    (hn : 128*(k-2)*(k.choose 2*((k.choose 2)^2).choose 2 + 1)^2 ≤ n) :
    UniformMaximizer m n k := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_large_boards hk hm hn

/-- The simpler sufficient dimension threshold k^21 for every order k ≥ 4. -/
theorem uniform_maximum_large_boards_power {m n k : ℕ} (hk : 4 ≤ k) (hm : k^21 ≤ m) (hn : k^21 ≤ n) :
    UniformMaximizer m n k := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_large_boards_power hk hm hn

/-- Every rectangular endpoint with smaller side at least 10^18, in both orientations. -/
theorem uniform_maximum_large_endpoints {m n : ℕ} (hm : 10^18 ≤ m) (hmn : m ≤ n) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_large_endpoints hm hmn

/-- The endpoint quadratic strip m ≥ 96 and n ≥ 10000 m^2, in both orientations. -/
theorem uniform_maximum_quadratic_endpoint_strip {m n : ℕ} (hm : 96 ≤ m) (hn : 10000*m^2 ≤ n) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_quadratic_endpoint_strip hm hn

/-- The endpoint quartic strip m ≥ 16 and n ≥ 20000 m^4, in both orientations. -/
theorem uniform_maximum_quartic_endpoint_strip {m n : ℕ} (hm : 16 ≤ m) (hn : 20000*m^4 ≤ n) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_quartic_endpoint_strip hm hn

/-- The endpoint strip m ≥ 5 and n ≥ 10^11 m^2, in both orientations. -/
theorem uniform_maximum_combined_endpoint_strip {m n : ℕ} (hm : 5 ≤ m) (hn : 100000000000*m^2 ≤ n) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_combined_endpoint_strip hm hn

/-- Consecutive dimensions m and m+1 for every m ≥ 19, in both orientations. -/
theorem uniform_maximum_consecutive_endpoint {m : ℕ} (hm : 19 ≤ m) :
    UniformMaximizer m (m+1) m ∧ UniformMaximizer (m+1) m m := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_consecutive_endpoint hm

/-- Every endpoint m ≤ n ≤ 2m with m ≥ 117, in both orientations. -/
theorem uniform_maximum_short_endpoint {m n : ℕ} (hm : 117 ≤ m) (hmn : m ≤ n) (hn : n ≤ 2*m) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_short_endpoint hm hmn hn

/-- Square near-endpoint order n−1 for every n ≥ 21. -/
theorem uniform_maximum_square_near_endpoint {n : ℕ} (hn : 21 ≤ n) : UniformMaximizer n n (n-1) := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_square_near_endpoint hn

/-- The logarithmic endpoint strip, with its positive-denominator cutoff cleared. -/
theorem uniform_maximum_arithmetic_endpoint {m n : ℕ} (hm : 128 ≤ m) (hmn : m ≤ n)
    (hcut : 22*(n : ℝ)*Real.log (m : ℝ) ≤ (m : ℝ)*((m : ℝ)-1)) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_arithmetic_endpoint hm hmn hcut

/-- The doubled endpoint n=2m for every m ≥ 80, in both orientations. -/
theorem uniform_maximum_double_endpoint {m : ℕ} (hm : 80 ≤ m) :
    UniformMaximizer m (2*m) m ∧ UniformMaximizer (2*m) m m := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_double_endpoint hm

/-- The local-lemma endpoint strip in exact integer form, including both edges and orientations. -/
theorem uniform_maximum_lll_endpoint {m n : ℕ} (hm : 128 ≤ m) (hmn : m ≤ n)
    (hlower : 4096*m^3 ≤ n^2) (hupper : 20*n ≤ m*(m-1)) :
    UniformMaximizer m n m ∧ UniformMaximizer n m m := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_lll_endpoint hm hmn hlower hupper

/-- All admissible orders when the smaller side is at most four. -/
theorem uniform_maximum_small_side {m n k : ℕ} (hsmall : min m n ≤ 4) (hk : 2 ≤ k)
    (hkmn : k ≤ min m n) : UniformMaximizer m n k := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_small_side hsmall hk hkmn

/-- Every admissible order two through five on the five-by-five simplex. -/
theorem uniform_maximum_five_by_five {k : ℕ} (hk : 2 ≤ k) (hk5 : k ≤ 5) : UniformMaximizer 5 5 k := by
  simpa only [← maximizer_eq] using DittertRybin.uniform_maximum_five_by_five hk hk5

end DittertRybinRelease
