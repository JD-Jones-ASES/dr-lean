import DR.Rectangular.OrderThreeFourRowFinal

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- The unconditioned pair kernel is not PSD; the row-neighborhood hypothesis matters.
example : quadraticValue (orderThreeFourRowPairKernel (fun i => if i.val=0 then 1 else 0))
    (fun i => if i.val=0 then -2 else 1)=(-5:ℝ) := by
  simp only [quadraticValue,orderThreeFourRowPairKernel,Fin.sum_univ_four]
  norm_num [Fin.ext_iff]

-- Deleting the entire mass gives the zero kernel, including signed test vectors.
example (x : Fin 4 → ℝ) : quadraticValue
    (orderThreeFourRowPairKernel (fun _ => (1/4:ℝ)-(1/4:ℝ))) x=0 := by
  simp [quadraticValue,orderThreeFourRowPairKernel]

-- No sign or total-mass condition is hidden in the actual kernel identification.
example {n : ℕ} (P : Board 4 n) :
    averagingKernel P 1=orderThreeFourRowPairKernel (rowSum P) :=
  averagingKernel_one_four_rows P
private def negativeMassBoard : Board 4 1 := fun _ _ => -1
example : averagingKernel negativeMassBoard 1 0 0=(-4:ℝ) := by
  rw [averagingKernel_one_diagonal]
  norm_num [negativeMassBoard,totalMass,rowSum]

-- The closed row-variance boundary 1/64 is retained by the quadratic floor.
example (x : Fin 4 → ℝ) : (1/4:ℝ)*(∑ i,x i^2)≤
    quadraticValue (orderThreeFourRowPairKernel
      (fun i => if i.val%2=0 then 5/16 else 3/16)) x := by
  apply orderThreeFourRowPairKernel_near_lower
  · norm_num [Fin.sum_univ_four]
  · norm_num [orderThreeFourRowVariance,Fin.sum_univ_four]

-- The quadratic estimate is for all real vectors; column entries may vanish.
example {n : ℕ} (hn : 960≤n) {P : Board 4 n} (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 3≤separationProbability P 3)
    (a b : Fin n) (hab : a≠b) (x : Fin 4 → ℝ) :
    (1/8:ℝ)*(∑ i,x i^2)≤quadraticValue (averagingKernel (eraseColumns P {a,b}) 1) x :=
  orderThreeFourRow_contender_kernel_lower hn hP hcont a b hab x

example {n : ℕ} (hn : 960≤n) : UniformMaximizer 4 n 3 :=
  uniformMaximizer_orderThree_four_rows hn
example {m : ℕ} (hm : 960≤m) : UniformMaximizer m 4 3 :=
  uniformMaximizer_orderThree_four_columns hm
example : UniformMaximizer 4 960 3 := uniformMaximizer_orderThree_four_rows (by norm_num)
example : UniformMaximizer 104729 4 3 := uniformMaximizer_orderThree_four_columns (by norm_num)

#print axioms orderThreeFourRowPairKernel_near_lower
#print axioms orderThreeFourRowPairKernel_deleted_lower
#print axioms averagingKernel_one_four_rows
#print axioms orderThreeFourRow_contender_blend_gain
#print axioms uniformMaximizer_orderThree_four_rows
#print axioms uniformMaximizer_orderThree_four_columns
end DittertRybin.Tests
