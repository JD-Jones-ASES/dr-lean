import DR.Endpoint.RowEndpointKernelPositive
import DR.Collision.Deletion

/-! The three localized scalar bounds needed by the endpoint kernel,
derived from a genuine normalized row law and a column-load square bound.
No upper bound on the total collision intensity is required. -/
namespace DittertRybin
open scoped BigOperators

theorem rowCollision_localized_kernel_bounds {m n : ℕ} (hm : 1≤m)
    (X : Board m n) (hX : ∀ i j,0≤X i j) (hs : ∀ i,rowSum X i=1)
    (C : ℝ) (hC0 : 0≤C) (hcap : ∀ j,colSum X j≤C)
    (hC : (m:ℝ)*C^2≤1/256) :
    0<rowAvoidance X ∧
    (∑ i,rowLocalizedDoubletonLoad X i)/(m:ℝ)≤1/4 ∧
    (∑ i,(rowLocalizedDoubletonLoad X i-
      (∑ j,rowLocalizedDoubletonLoad X j)/(m:ℝ))^2)≤1/64 ∧
    ∀ i,rowLocalizedDeficitTwoLoad X i≤1/4 := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hCsq : C^2≤1/256 := by nlinarith [sq_nonneg C]
  have hCsmall : C≤1/16 := by nlinarith
  have hd (i : Fin m) : rowCollisionLoad X i≤1/8 :=
    (rowCollisionLoad_le_column_cap X hX hs hcap i).trans (by linarith)
  have ht0 (i : Fin m) : 0≤rowLocalizedDoubletonLoad X i :=
    rowLocalizedDoubletonLoad_nonneg X hX i
  have ht (i : Fin m) : rowLocalizedDoubletonLoad X i≤(16/9)*C := by
    exact (rowLocalizedDoubletonLoad_le X hX hs hd i).trans
      (mul_le_mul_of_nonneg_left (rowCollisionLoad_le_column_cap X hX hs hcap i)
        (by norm_num))
  have htmean : (∑ i,rowLocalizedDoubletonLoad X i)/(m:ℝ)≤1/4 := by
    apply (div_le_iff₀ hm0).mpr
    have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => ht i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    nlinarith
  have htsq : (∑ i,(rowLocalizedDoubletonLoad X i)^2)≤(256/81)*(m:ℝ)*C^2 := by
    have hi (i : Fin m) : (rowLocalizedDoubletonLoad X i)^2≤((16/9)*C)^2 := by
      nlinarith [ht i,ht0 i]
    have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
    apply hsum.trans_eq
    ring
  have hc := sum_sq_center_le (by omega : 0<m) (rowLocalizedDoubletonLoad X) 0
  simp only [sub_zero] at hc
  refine ⟨rowAvoidance_pos_of_collisionLoad X hX hs hd,htmean,?_,?_⟩
  · nlinarith only [hc,htsq,hC]
  · intro i
    have hv := rowLocalizedDeficitTwoLoad_le_columnCap X hX hs hd C hcap i
    nlinarith only [hv,hCsq,hC]

end DittertRybin
