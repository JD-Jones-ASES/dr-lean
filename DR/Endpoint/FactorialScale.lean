import DR.Certificates.SpectralParameters

/-! The exact all-dimension factorial guard used after the elementary lower
bound in the endpoint collision criterion. -/
namespace DittertRybin
open Certificates.SpectralParameters

/-- Multiplication by 2 at each dimension cancels the factorial ratio bound. -/
theorem endpoint_scaled_factorial_succ {m : ℕ} (hm : 2≤m) :
    (2:ℝ)^(m+1-2)*dittertConstant (m+1)≤(2:ℝ)^(m-2)*dittertConstant m := by
  have h := gamma_succ_le_half (by omega : 0<m)
  rw [show m+1-2=m-2+1 by omega,pow_succ]
  calc
    _≤((2:ℝ)^(m-2)*2)*(dittertConstant m/2) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _=_ := by ring

/-- Exact base arithmetic and induction, not an extrapolated finite scan. -/
theorem endpoint_scaled_factorial_lt_one_thirty_two {m : ℕ} (hm : 16≤m) :
    (2:ℝ)^(m-2)*dittertConstant m<1/32 := by
  have hbase : (2:ℝ)^(16-2)*dittertConstant 16<1/32 := by
    norm_num [dittertConstant,Nat.factorial]
  apply lt_of_le_of_lt _ hbase
  induction m,hm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact (endpoint_scaled_factorial_succ (by omega)).trans ih

end DittertRybin
