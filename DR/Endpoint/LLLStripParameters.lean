import DR.Endpoint.UniformAvoidanceBound
import DR.Endpoint.LargeRowCaps

/-! Exact integer-to-real parameter guards for the accepted LLL endpoint
strip. The lower edge is written n²≥4096m³, equivalent to the source's
n≥64m^(3/2) on nonnegative dimensions. -/
namespace DittertRybin

theorem endpoint_strip_n_ge {m n : ℕ} (hm : 1≤m)
    (hlower : 4096*m^3≤n^2) : 64*m≤n := by
  have hpow : m^2≤m^3 := by nlinarith [Nat.mul_le_mul_left (m^2) hm]
  nlinarith

theorem endpoint_strip_n_le_square {m n : ℕ}
    (hupper : 20*n≤m*(m-1)) : n≤m^2 := by
  have h := Nat.mul_le_mul_left m (Nat.sub_le m 1)
  nlinarith

theorem endpoint_strip_cap_sq {m n : ℕ} (hm : 1≤m)
    (hlower : 4096*m^3≤n^2) : (m:ℝ)*(4*(m:ℝ)/(n:ℝ))^2≤1/256 := by
  have hn : 0<n := by have := endpoint_strip_n_ge hm hlower; omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hlow : (4096:ℝ)*(m:ℝ)^3≤(n:ℝ)^2 := by exact_mod_cast hlower
  have hid : (m:ℝ)*(4*(m:ℝ)/(n:ℝ))^2=16*(m:ℝ)^3/(n:ℝ)^2 := by ring
  rw [hid]
  apply (div_le_iff₀ (sq_pos_of_pos hnR)).mpr
  nlinarith

theorem endpoint_strip_deletion_scale {m n : ℕ} (hm : 1≤m)
    (hlower : 4096*m^3≤n^2) : (m:ℝ)*(4/(n:ℝ))≤1/16 := by
  have hn : 0<n := by have := endpoint_strip_n_ge hm hlower; omega
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hlow : (64:ℝ)*(m:ℝ)≤n := by exact_mod_cast endpoint_strip_n_ge hm hlower
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hnR).mpr
  nlinarith

/-- The actual contender column cap, with all zero-cell boundary points included. -/
theorem endpoint_strip_contender_column_cap {m n : ℕ} (hm : 128≤m)
    (hmn : m≤n) (hupper : 20*n≤m*(m-1)) {P : Board m n}
    (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m) (j : Fin n) :
    colSum P j<2/(n:ℝ) := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast (by omega : 1≤m)
  have hnR : (0:ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hn2 : (n:ℝ)≤(m:ℝ)^2 := by exact_mod_cast endpoint_strip_n_le_square hupper
  have hm4 : (n:ℝ)≤(m:ℝ)^4 := by
    have hm2 : (1:ℝ)≤(m:ℝ)^2 := by nlinarith
    nlinarith [sq_nonneg ((m:ℝ)^2-1)]
  have hinv : 1/(m:ℝ)^4≤1/(n:ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) hnR hm4
  have h := endpoint_contender_column_cap_large hm hmn hP hcont j
  calc
    colSum P j<1/(n:ℝ)+1/(m:ℝ)^4 := h
    _≤1/(n:ℝ)+1/(n:ℝ) := add_le_add le_rfl hinv
    _=2/(n:ℝ) := by ring

end DittertRybin
