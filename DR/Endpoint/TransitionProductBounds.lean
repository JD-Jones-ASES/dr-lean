import DR.Endpoint.RowProductConcentration

/-! Coarse closed-simplex product bounds used by the accepted large-m
endpoint transition argument. These are scalar finite-product statements,
not assumptions about a stationary matrix or optimizer shape. -/
namespace DittertRybin
open scoped BigOperators

theorem coordinate_exp_envelope_le_at (a y : ℝ) (ha : 1≤a) (hy : a≤y) :
    y*Real.exp (1-y)≤a*Real.exp (1-a) := by
  have ht := Real.add_one_le_exp (y-a)
  have hmul := mul_le_mul_of_nonneg_left ht (by linarith : 0≤a)
  have h : y≤a*Real.exp (y-a) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hy)]
  have hscale := mul_le_mul_of_nonneg_right h (Real.exp_pos (1-y)).le
  apply hscale.trans_eq
  rw [mul_assoc,← Real.exp_add]
  congr 2
  ring

theorem exp_neg_one_lt_half : Real.exp (-1)<(1/2:ℝ) := by
  rw [Real.exp_neg,inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
  linarith [Real.exp_one_gt_d9]

theorem thirty_two_exp_neg_thirty_one_lt : (32:ℝ)*Real.exp (-31)<1/50000 := by
  have hp := pow_lt_pow_left₀ exp_neg_one_lt_half (Real.exp_pos (-1)).le
    (by decide : (31:ℕ)≠0)
  have he : Real.exp (-31)=(Real.exp (-1))^31 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he]
  have hs := mul_lt_mul_of_pos_left hp (by norm_num : (0:ℝ)<32)
  exact hs.trans (by norm_num)

theorem exp_neg_sixteen_lt_inv50000 : Real.exp (-16)<(1:ℝ)/50000 := by
  have hp := pow_lt_pow_left₀ exp_neg_one_lt_half (Real.exp_pos (-1)).le
    (by decide : (16:ℕ)≠0)
  have he : Real.exp (-16)=(Real.exp (-1))^16 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he]
  exact hp.trans (by norm_num)

theorem log_le_sub_one_sub_sq_sixty_four (y : ℝ) (hy : 0<y) (hy32 : y≤32) :
    Real.log y≤y-1-(y-1)^2/64 := by
  let r := Real.sqrt y
  have hr : 0<r := Real.sqrt_pos.mpr hy
  have hrsq : r^2=y := Real.sq_sqrt hy.le
  have hrupper : r≤7 := by nlinarith
  have hlog := Real.log_le_sub_one_of_pos hr
  have hlogs : Real.log r=Real.log y/2 := Real.log_sqrt hy.le
  rw [hlogs] at hlog
  have hnonneg : 0≤(r-1)^2*(64-(r+1)^2) :=
    mul_nonneg (sq_nonneg _) (by nlinarith)
  have hsq : (y-1)^2≤64*(r-1)^2 := by nlinarith [sq_nonneg (r-1)]
  nlinarith

theorem transition_product_coordinate_bounds {d : ℕ} (y : Fin d → ℝ)
    (hy : ∀ i,0≤y i) (hs : ∑ i,y i=d) (hp : 1/50000<∏ i,y i) (i : Fin d) :
    1/150000<y i ∧ y i<32 := by
  have hypos : 0<y i := by
    by_contra hn
    have hz : y i=0 := le_antisymm (le_of_not_gt hn) (hy i)
    have hpz : (∏ j,y j)=0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [hpz] at hp
    norm_num at hp
  have henv := product_le_coordinate_mul_exp hy hs i
  have he : Real.exp (1-y i)<3 :=
    ((Real.exp_lt_exp.mpr (by linarith : 1-y i<1)).trans Real.exp_one_lt_three)
  have hlow := mul_lt_mul_of_pos_left he hypos
  refine ⟨by nlinarith,?_⟩
  by_contra hn
  have hupper := henv.trans (coordinate_exp_envelope_le_at 32 (y i) (by norm_num) (le_of_not_gt hn))
  have hu : (32:ℝ)*Real.exp (1-32)<1/50000 := by
    norm_num only [show (1:ℝ)-32 = -31 by norm_num]
    exact thirty_two_exp_neg_thirty_one_lt
  exact (not_lt_of_ge hupper) (hu.trans hp)

theorem transition_product_sq_deviation {d : ℕ} (y : Fin d → ℝ)
    (hy : ∀ i,0≤y i) (hs : ∑ i,y i=d) (hp : 1/50000<∏ i,y i) :
    (∑ i,(y i-1)^2)<1024 := by
  have hi (i : Fin d) := transition_product_coordinate_bounds y hy hs hp i
  have hipos (i : Fin d) : 0<y i := lt_trans (by norm_num) (hi i).1
  have h := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    log_le_sub_one_sub_sq_sixty_four (y i) (hipos i) (hi i).2.le)
  have hlogs : (∑ i,Real.log (y i))=Real.log (∏ i,y i) :=
    (Real.log_prod (fun i _ => (hipos i).ne')).symm
  have hsum : (∑ i,(y i-1))=0 := by
    simp only [Finset.sum_sub_distrib,hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,mul_one,sub_self]
  rw [hlogs,Finset.sum_sub_distrib,hsum,← Finset.sum_div] at h
  have hloglow : (-16:ℝ)<Real.log (∏ i,y i) := by
    have hl := Real.log_lt_log (Real.exp_pos (-16)) (exp_neg_sixteen_lt_inv50000.trans hp)
    simpa only [Real.log_exp] using hl
  linarith

theorem transition_product_reciprocal_deviation {d : ℕ} (y : Fin d → ℝ)
    (hy : ∀ i,0≤y i) (hs : ∑ i,y i=d) (hp : 1/50000<∏ i,y i) :
    (∑ i,(y i-1)^2/y i)<160000000 := by
  have hsq := transition_product_sq_deviation y hy hs hp
  have hi (i : Fin d) : (y i-1)^2/y i≤150000*(y i-1)^2 := by
    have hlo := (transition_product_coordinate_bounds y hy hs hp i).1
    have h := div_le_div_of_nonneg_left (sq_nonneg (y i-1))
      (by norm_num : (0:ℝ)<1/150000) hlo.le
    apply h.trans_eq
    ring
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hi i)
  rw [← Finset.mul_sum] at hsum
  linarith

end DittertRybin
