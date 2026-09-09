import DR.Rectangular.FourRowMinorantStationaryMin
import DR.Rectangular.FourRowMinorantOneLarge

open DittertRybin
open scoped BigOperators

-- The original full v simplex is the minimization domain in this expanded statement.
example (r v : Fin 4 → ℝ) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    (hv : ∀ i,0<v i) (hvs : ∑ i,v i=1)
    (hmin : ∀ w : Fin 4 → ℝ, (∀ i,0≤w i) → (∑ i,w i)=1 →
      fourRowMinorantHomogeneous r v ≤ fourRowMinorantHomogeneous r w) :
    fourRowMinorantSquareSum r < 1/3 ∧ v=fourRowMinorantStationary r :=
  ⟨IsFourRowMinorantMinimum.squareSum_lt hmin hr hs hv hvs,
    IsFourRowMinorantMinimum.eq_stationary hmin hr hs hv hvs⟩

private noncomputable def singularRows : Fin 4 → ℝ := ![1/2,1/6,1/6,1/6]

private theorem singularRows_sum : (∑ i,singularRows i)=1 := by
  norm_num [singularRows, Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

private theorem singularRows_squareSum : fourRowMinorantSquareSum singularRows = 1/3 := by
  norm_num [singularRows, fourRowMinorantSquareSum, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]

-- A zero quadratic direction at q=1/3 still has a nonzero linear derivative.
example : fourRowMinorantQuadratic singularRows (fourRowMinorantConcentrationDirection singularRows)=0 := by
  rw [fourRowMinorantConcentrationDirection_quadratic _ singularRows_sum]
  norm_num [fourRowMinorantDelta, singularRows_squareSum]

example : (∑ i,fourRowMinorantGradient singularRows (fun _ => 1/4) i *
    fourRowMinorantConcentrationDirection singularRows i) = -1/648 := by
  rw [fourRowMinorantConcentrationDirection_gradient _ _ singularRows_sum (by norm_num)]
  simp only [fourRowMinorantDelta, singularRows_squareSum]
  norm_num [singularRows, Fin.prod_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]

example (v : Fin 4 → ℝ) (hv : ∀ i,0<v i) (hvs : ∑ i,v i=1) :
    ¬ IsFourRowMinorantMinimum singularRows v := by
  intro hmin
  have hr : ∀ i,0<singularRows i := by
    intro i
    fin_cases i <;> norm_num [singularRows, Matrix.cons_val_two, Matrix.cons_val_three]
  have hq := hmin.squareSum_lt hr singularRows_sum hv hvs
  rw [singularRows_squareSum] at hq
  exact lt_irrefl _ hq

-- The tangent criterion identifies actual vectors; it does not need a feasibility hypothesis for x.
example (r w : Fin 4 → ℝ) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    (hq : fourRowMinorantSquareSum r<1/3) (hw : ∑ i,w i=0)
    (hQ : fourRowMinorantQuadratic r w=0) : w=0 :=
  fourRowMinorantQuadratic_tangent_zero r w hr hs hq hw hQ

#print axioms fourRowMinorant_line
#print axioms IsFourRowMinorantMinimum.line_localMin
#print axioms IsFourRowMinorantMinimum.squareSum_lt
#print axioms fourRowMinorant_tangent_cauchy
#print axioms IsFourRowMinorantMinimum.eq_stationary
