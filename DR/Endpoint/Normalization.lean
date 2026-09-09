import DR.Endpoint.RowProduct
import DR.ElementarySymmetricBoundsVariance

/-!
# Exact normalization at the rectangular endpoint

For m draws from an m-by-n board, write a=m!/m^m and b=(n)_m/n^m.
The actual inclusive-OR functional equals a R+b S-a T, where R is the
normalized row product, S the normalized column elementary sum, and T
the normalized rook sum. These are polynomial identities on signed boards;
normalizing the independent original-row law is a separate step requiring
nonzero row sums. No optimization or gauge inequality is assumed here.
-/

namespace DittertRybin
open scoped BigOperators

noncomputable def endpointRowProduct {m n : ℕ} (P : Board m n) : ℝ :=
  (m:ℝ)^m*∏ i, rowSum P i

noncomputable def endpointColumnRatio {m n : ℕ} (P : Board m n) : ℝ :=
  normalizedElementarySuccess (colSum P) m

noncomputable def endpointRookRatio {m n : ℕ} (P : Board m n) : ℝ :=
  (m:ℝ)^m*rookSum P m

noncomputable def endpointRookDeficit {m n : ℕ} (P : Board m n) : ℝ :=
  distinctUniformProbability n m-endpointRookRatio P

/-- The original board's normalized independent-row law. A deleted board
must be supplied as a different argument and has its own normalization. -/
noncomputable def originalRowAvoidance {m n : ℕ} (P : Board m n) : ℝ :=
  rowAvoidance (normalizeRows P)

theorem distinctUniformProbability_pos {d k : ℕ} (hd : 0 < d) (hk : k ≤ d) :
    0 < distinctUniformProbability d k := by
  exact div_pos (by exact_mod_cast Nat.descFactorial_pos.mpr hk)
    (pow_pos (by exact_mod_cast hd) _)

theorem distinctUniformProbability_lt_one {d k : ℕ} (hd : 0 < d) (hk : 2 ≤ k) :
    distinctUniformProbability d k < 1 := by
  rw [distinctUniformProbability,div_lt_one (pow_pos (by exact_mod_cast hd) _)]
  exact_mod_cast Nat.descFactorial_lt_pow hd.ne' hk

theorem distinctUniformProbability_self (d : ℕ) :
    distinctUniformProbability d d = dittertConstant d := by
  simp only [distinctUniformProbability,dittertConstant,Nat.descFactorial_self]

theorem endpoint_a_pos {m : ℕ} (hm : 0 < m) : 0 < dittertConstant m := by
  rw [← distinctUniformProbability_self]
  exact distinctUniformProbability_pos hm le_rfl

theorem endpoint_a_lt_one {m : ℕ} (hm : 2 ≤ m) : dittertConstant m < 1 := by
  rw [← distinctUniformProbability_self]
  exact distinctUniformProbability_lt_one (by omega) hm

theorem elementarySymmetric_top {d : ℕ} (x : Fin d → ℝ) :
    elementarySymmetric x d = ∏ i, x i := by
  rw [elementarySymmetric_eq_powerset_sum]
  have hh : (Finset.univ : Finset (Fin d)).powersetCard d = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin d))
  rw [hh]
  simp

theorem endpointRowProduct_eq_normalized {m n : ℕ} (P : Board m n) :
    endpointRowProduct P = normalizedElementarySuccess (rowSum P) m := by
  simp only [normalizedElementarySuccess,elementaryMean,elementarySymmetric_top,
    Nat.choose_self,Nat.cast_one,div_one,endpointRowProduct]

theorem endpointRowProduct_eq_product {m n : ℕ} (P : Board m n) :
    endpointRowProduct P = ∏ i, (m:ℝ)*rowSum P i := by
  simp [endpointRowProduct,Finset.prod_mul_distrib]

theorem separationProbability_endpoint_ratios {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    (P : Board m n) :
    separationProbability P m = dittertConstant m*endpointRowProduct P+
      distinctUniformProbability n m*endpointColumnRatio P-
      dittertConstant m*endpointRookRatio P := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hc : (n.choose m:ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmn).ne'
  rw [separationProbability_eq_rook,elementarySymmetric_top]
  simp only [dittertConstant,endpointRowProduct,endpointColumnRatio,endpointRookRatio,
    normalizedElementarySuccess,elementaryMean,distinctUniformProbability,
    Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  field_simp

theorem uniformSeparationValue_rectangular_endpoint (m n : ℕ) :
    uniformSeparationValue m n m = dittertConstant m+distinctUniformProbability n m-
      dittertConstant m*distinctUniformProbability n m := by
  simp only [uniformSeparationValue,distinctUniformProbability_self]

/-- No factorial appears when conditioning on one independent column choice per row. -/
theorem endpointRookRatio_eq_originalRowAvoidance {m n : ℕ} (P : Board m n)
    (hr : ∀ i, rowSum P i ≠ 0) :
    endpointRookRatio P = endpointRowProduct P*originalRowAvoidance P := by
  rw [endpointRookRatio,rookSum_endpoint_normalized P hr]
  simp only [endpointRowProduct,originalRowAvoidance,mul_assoc]

theorem rowAvoidance_const {m n : ℕ} (c : ℝ) :
    rowAvoidance (fun _ : Fin m => fun _ : Fin n => c) = (n.descFactorial m:ℝ)*c^m := by
  simp [rowAvoidance,rowAssignmentMass,Fintype.card_embedding_eq,nsmul_eq_mul]

theorem normalizeRows_uniformBoard {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    normalizeRows (uniformBoard m n) = fun _ _ => 1/(n:ℝ) := by
  have hm0 : (m:ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  funext i j
  simp [normalizeRows,rowSum,uniformBoard]
  field_simp

theorem originalRowAvoidance_uniform {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    originalRowAvoidance (uniformBoard m n) = distinctUniformProbability n m := by
  rw [originalRowAvoidance,normalizeRows_uniformBoard hm hn,rowAvoidance_const]
  simp [distinctUniformProbability,div_eq_mul_inv]

end DittertRybin
