import DR.Endpoint.LeadingKernel
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

-- The complementary-product kernel is polynomial on signed and boundary rows.
example (i j : Fin 3) :
    (![0,-2,3] : Fin 3 → ℝ) i*(![0,-2,3] : Fin 3 → ℝ) j*
      endpointLeadingKernel ![0,-2,3] i j =
      (if i=j then endpointLeadingScale ![0,-2,3] else 0)+
      (![0,-2,3] : Fin 3 → ℝ) i*(![0,-2,3] : Fin 3 → ℝ) j-
      endpointLeadingScale ![0,-2,3] :=
  endpointLeadingKernel_conjugacy _ i j
example : endpointLeadingScale (![0,-2,3] : Fin 3 → ℝ)=0 := by
  norm_num [endpointLeadingScale,Fin.prod_univ_succ]
example (x : Fin 0 → ℝ) :
    quadraticValue (endpointLeadingKernel (0 : Fin 0 → ℝ)) x=0 := by
  simp [quadraticValue]

-- The ordinary all-rows PSD conclusion is not assumed: it is false even
-- at a positive mass-one marginal in the intended m>=5 range.
example : quadraticValue (endpointLeadingKernel
      (![9/10,1/40,1/40,1/40,1/40] : Fin 5 → ℝ)) ![-4,1,1,1,1] = -3/80 := by
  let r : Fin 5 → ℝ := ![9/10,1/40,1/40,1/40,1/40]
  let y : Fin 5 → ℝ := ![-40/9,40,40,40,40]
  have he : (fun i => r i*y i)=(![-4,1,1,1,1] : Fin 5 → ℝ) := by
    funext i
    fin_cases i <;> norm_num [r,y]
  have h := endpointLeadingKernel_scaled_quadratic r y
  rw [he] at h
  norm_num [r,y,endpointLeadingScale,Nat.factorial,Fin.sum_univ_succ,Fin.prod_univ_succ] at h
  simpa only [neg_div] using h


-- The proved marginal criterion does include the uniform five-row kernel.
example : (endpointLeadingKernel (fun _ : Fin 5 => (1/5:ℝ))).PosDef := by
  apply endpointLeadingKernel_posDef
  · norm_num
  · norm_num
  · norm_num [endpointLeadingScale,Nat.factorial]

-- The rank-one Cauchy calculation accepts zero coordinates and signed x.
example (x : Fin 3 → ℝ) :
    (1/7:ℝ)*(∑ i,x i)^2 ≤
      (3-1/((∑ i,(![0,1/3,2/3] : Fin 3 → ℝ) i^2)+1/7))*
        ((1/7)*(∑ i,x i^2)+(∑ i,(![0,1/3,2/3] : Fin 3 → ℝ) i*x i)^2) := by
  apply endpoint_rank_one_cauchy _ x
  · norm_num [Fin.sum_univ_succ]
  · norm_num

#print axioms endpointLeadingKernel_conjugacy
#print axioms endpointLeadingKernel_scaled_quadratic
#print axioms endpoint_rank_one_cauchy
#print axioms endpointLeadingKernel_scaled_rank_one_lower
#print axioms endpointLeadingKernel_posDef

end DittertRybin.Tests
