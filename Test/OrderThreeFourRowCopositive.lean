import DR.Rectangular.OrderThreeFourRowCopositive

namespace DittertRybin.Tests
open scoped BigOperators

-- Completion is an identity for signed row masses; the minimizer need not lie in the row simplex.
example : orderThreeFourRowD ![2,-1,0,0] ![1,0,0,0] = 2 := by
  norm_num [orderThreeFourRowD,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three]

-- The singular e3=0 boundary can attain equality and is retained by the continuity proof.
example : orderThreeFourRowE3 ![1,0,0,0]=0 ∧ orderThreeFourRowD ![1,0,0,0] ![1,0,0,0]=0 := by
  have hc (i : Fin 4) : orderThreeFourRowCofactor ![1,0,0,0] i=0 := by
    fin_cases i <;> norm_num [orderThreeFourRowCofactor,Fin.add_def,Matrix.cons_val_two,Matrix.cons_val_three]
  constructor
  · simp only [orderThreeFourRowE3,hc,Finset.sum_const_zero]
  · norm_num [orderThreeFourRowD,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three]

example (r v : Fin 4 → ℝ) (hr : ∑ i,r i=1) (hv : ∑ i,v i=1) (hv0 : ∀ i,0≤v i) :
    0≤orderThreeFourRowD r v := orderThreeFourRowD_nonneg r v hr hv hv0

-- The homogeneous extension includes a zero column exactly.
example (r : Fin 4 → ℝ) : orderThreeFourRowQuadratic r (fun _=>0)=0 := by
  simp [orderThreeFourRowQuadratic]

example (r v : Fin 4 → ℝ) (hr0 : ∀ i,0≤r i) (hr : ∑ i,r i=1) (hv0 : ∀ i,0≤v i) :
    (∑ i,v i*orderThreeFourRowWeight (r i))^2≤orderThreeFourRowQuadratic r v :=
  orderThreeFourRowQuadratic_lower r v hr0 hr hv0

-- Copositivity is essential: this signed column makes the rank-one minorant false.
example : ¬ ((∑ i : Fin 4, (![1,-1,0,0] : Fin 4 → ℝ) i *
    orderThreeFourRowWeight ((![1,0,0,0] : Fin 4 → ℝ) i))^2 ≤
      orderThreeFourRowQuadratic ![1,0,0,0] ![1,-1,0,0]) := by
  have hsum : (∑ i : Fin 4, (![1,-1,0,0] : Fin 4 → ℝ) i *
      orderThreeFourRowWeight ((![1,0,0,0] : Fin 4 → ℝ) i)) = 1-Real.sqrt (1/3:ℝ) := by
    norm_num [orderThreeFourRowWeight,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three]
    ring
  have hq : orderThreeFourRowQuadratic ![1,0,0,0] ![1,-1,0,0]=0 := by
    norm_num [orderThreeFourRowQuadratic,Fin.sum_univ_four,Matrix.cons_val_two,Matrix.cons_val_three]
  rw [hsum,hq]
  intro h
  have hz := sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _))
  have he : Real.sqrt (1/3:ℝ)=1 := by linarith only [hz]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤1/3)
  rw [he] at hs
  norm_num at hs

#print axioms orderThreeFourRowD_completion
#print axioms orderThreeFourRowD_nonneg
#print axioms orderThreeFourRowQuadratic_lower
end DittertRybin.Tests
