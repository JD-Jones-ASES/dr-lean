import DR.Endpoint.LeadingBoundary
import DR.Endpoint.LeadingRatioBounds
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

private noncomputable def boundaryBoard : Board 3 2 := !![0,0;1/2,0;0,1/2]
private theorem boundaryBoard_probability : IsProbability boundaryBoard := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [boundaryBoard]
  · norm_num [totalMass,rowSum,boundaryBoard,Fin.sum_univ_succ]

-- A genuine zero row fixes the entire leading gauge at one.
example : endpointLeadingGauge boundaryBoard=1 := by
  apply endpointLeadingGauge_zero_row boundaryBoard boundaryBoard_probability 0
  norm_num [rowSum,boundaryBoard,Fin.sum_univ_succ]
example : ¬endpointLeadingGauge boundaryBoard<1 := by
  rw [endpointLeadingGauge_zero_row boundaryBoard boundaryBoard_probability 0
    (by norm_num [rowSum,boundaryBoard,Fin.sum_univ_succ])]
  exact lt_irrefl 1

-- The zero row is not silently promoted to a normalized row law.
example : rowSum (normalizeRows boundaryBoard) 0=0 := by
  norm_num [rowSum,normalizeRows,boundaryBoard,Fin.sum_univ_succ]

-- The global minimum is on the full closed board simplex, for a nonlinear penalty too.
example : ∃ P : Board 3 2, IsEndpointGaugeMinimum P (fun q => q^2-7*q) := by
  apply exists_endpointGaugeMinimum (by decide) (by decide)
  fun_prop
example : Continuous (endpointLeadingGauge : Board 0 0 → ℝ) :=
  continuous_endpointLeadingGauge 0 0

-- Nonempty rows with an empty column: its zero ratio does not spoil A_i>=1.
example (i : Fin 3) :
    1≤endpointLeadingRowDerivative (fun _ : Fin 3 => 1/3) (!![1,0;1,0;1,0] : Board 3 2) i ∧
    endpointLeadingRowDerivative (fun _ : Fin 3 => 1/3) (!![1,0;1,0;1,0] : Board 3 2) i≤
      endpointLeadingRatioCap 3 := by
  apply endpointLeadingRowDerivative_bounds (by decide)
  · norm_num
  · norm_num
  · intro a j
    fin_cases a <;> fin_cases j <;> norm_num
  · intro a
    fin_cases a <;> norm_num [rowSum,Fin.sum_univ_succ]

example (X : Board 3 2) (hX : ∀ i j,0≤X i j) :
    0≤endpointLeadingMoment (![0,1/3,2/3] : Fin 3 → ℝ) X := by
  apply endpointLeadingMoment_nonneg _ X _ hX
  intro i
  fin_cases i <;> norm_num

-- This compactness-to-stationarity API still requires actual positive rows.
example {m n : ℕ} (hm : 3≤m) (P : Board m n) (psi : ℝ → ℝ)
    (hmin : IsEndpointGaugeMinimum P psi) (hG : endpointLeadingGauge P<1)
    (tau : ℝ) (hpsi : HasDerivAt psi tau (∑ i,(rowSum P i)^2)) (i : Fin m) :
    endpointLeadingRowDerivative (rowSum P) (normalizeRows P) i=
      endpointLeadingGauge P-((m:ℝ)-2)*endpointLeadingMoment (rowSum P) (normalizeRows P)+
      2*tau*(rowSum P i-(∑ a,(rowSum P a)^2))+
      endpointLeadingMoment (rowSum P) (normalizeRows P)/rowSum P i :=
  hmin.stationarity hm (endpointLeading_rows_pos_of_lt_one P hmin.1 hG) tau hpsi i

#print axioms endpointLeadingColumn_zero_row
#print axioms endpointLeadingGauge_zero_row
#print axioms endpointLeading_rows_pos_of_lt_one
#print axioms continuous_endpointLeadingGauge
#print axioms exists_endpointGaugeMinimum
#print axioms IsEndpointGaugeMinimum.row_minimum
#print axioms IsEndpointGaugeMinimum.stationarity
#print axioms endpointLeadingRowDerivative_bounds
#print axioms endpointLeadingMoment_nonneg
#print axioms endpointLeadingGauge_le_one
#print axioms endpointLeadingGauge_pos

end DittertRybin.Tests
