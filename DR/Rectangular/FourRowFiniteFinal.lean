import DR.Rectangular.FourRowFiniteFamilyCriterion
import DR.Rectangular.FourRowFiniteProbability

/-! Full closed-simplex K=4 maximization on4×N for the two finite intervals.
Every matrix gate and coefficient equation is discharged by the literal families. -/

namespace DittertRybin
open Certificates

theorem uniformMaximizer_orderFour_four_rows_five_fifty {n : ℕ}
    (hn : 5 ≤ n ∧ n ≤ 50) : UniformMaximizer 4 n 4 := by
  have hcrit := fourRowFinite5_entry_criterion hn.1 (fourRowFiniteParameter 5 n)
    (fourRowFiniteParameter_five hn)
    (fourRowFiniteParameter_dimension (by decide : 0 < 5) (by omega : 0 < n)).symm
  apply (fourRowFinite5_coefficientEquations (by omega : 4 ≤ n)).uniformMaximizer (by omega)
    (fun t => (hcrit t).1)
  intro e p hp
  exact ((hcrit (fun _ => e)).2 p).mp hp

theorem uniformMaximizer_orderFour_four_rows_fifty_fiveHundred {n : ℕ}
    (hn : 50 ≤ n ∧ n ≤ 500) : UniformMaximizer 4 n 4 := by
  have hcrit := fourRowFinite50_entry_criterion (by omega : 5 ≤ n) (fourRowFiniteParameter 50 n)
    (fourRowFiniteParameter_fifty hn)
    (fourRowFiniteParameter_dimension (by decide : 0 < 50) (by omega : 0 < n)).symm
  apply (fourRowFinite50_coefficientEquations (by omega : 4 ≤ n)).uniformMaximizer (by omega)
    (fun t => (hcrit t).1)
  intro e p hp
  exact ((hcrit (fun _ => e)).2 p).mp hp

theorem uniformMaximizer_orderFour_four_rows_finite {n : ℕ}
    (hn : 5 ≤ n ∧ n ≤ 500) : UniformMaximizer 4 n 4 := by
  by_cases h : n ≤ 50
  · exact uniformMaximizer_orderFour_four_rows_five_fifty ⟨hn.1,h⟩
  · exact uniformMaximizer_orderFour_four_rows_fifty_fiveHundred ⟨by omega,hn.2⟩

end DittertRybin
