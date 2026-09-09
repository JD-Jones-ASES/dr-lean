import DR.Rectangular.FourRowMinorantVariations

/-! Strict tangent curvature identifies the stationary vector of every positive minimizer. -/

namespace DittertRybin
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem fourRowMinorantQuadratic_scaled (r x : Fin 4 → ℝ) (hs : ∑ i,r i=1) :
    fourRowMinorantQuadratic r (fun i => r i*x i) =
      2*(∏ i,r i)*((∑ i,x i^2)-(∑ i,x i)^2) := by
  norm_num [fourRowMinorantQuadratic, hs, fourRow_complement_product,
    Fin.sum_univ_succ, Fin.prod_univ_succ, Finset.sum_erase,
    Fin.ext_iff, -Fin.val_eq_zero_iff]
  ring

/-- The projection form of finite Cauchy--Schwarz, without inverse row coordinates. -/
theorem fourRowMinorant_tangent_cauchy (r x : Fin 4 → ℝ) (hs : ∑ i,r i=1)
    (hx : ∑ i,r i*x i=0) :
    fourRowMinorantSquareSum r*(∑ i,x i)^2 ≤
      (4*fourRowMinorantSquareSum r-1)*(∑ i,x i^2) := by
  let q := fourRowMinorantSquareSum r
  have hq : 0 < q := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ r (fun _ => (1:ℝ))
    simp only [mul_one, hs, one_pow, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at h
    change (1:ℝ) ≤ q*4 at h
    linarith
  have hsum : (∑ i,(q-r i)*x i) = q*(∑ i,x i) := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hx, sub_zero]
  have hsquares : (∑ i,(q-r i)^2) = q*(4*q-1) := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hs]
    change 4*q^2-2*q*1+q = q*(4*q-1)
    ring
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => q-r i) x
  rw [hsum, hsquares] at hc
  apply (mul_le_mul_iff_right₀ hq).mp
  nlinarith [hc]

/-- Below q=1/3 the zero tangent quadratic has only the zero vector. -/
theorem fourRowMinorantQuadratic_tangent_zero (r w : Fin 4 → ℝ)
    (hr : ∀ i, 0 < r i) (hs : ∑ i,r i=1)
    (hq : fourRowMinorantSquareSum r < 1/3) (hw : ∑ i,w i=0)
    (hQ : fourRowMinorantQuadratic r w=0) : w=0 := by
  let x : Fin 4 → ℝ := fun i => w i/r i
  have hfactor : (fun i => r i*x i) = w := by
    funext i
    dsimp [x]
    field_simp [(hr i).ne']
  have hx : (∑ i,r i*x i)=0 := by rw [show (fun i => r i*x i)=w from hfactor]; exact hw
  have hprod : 0 < 2*(∏ i,r i) := mul_pos (by norm_num) (Finset.prod_pos (fun i _ => hr i))
  have hQ' := fourRowMinorantQuadratic_scaled r x hs
  rw [hfactor,hQ] at hQ'
  have hsq : (∑ i,x i^2)=(∑ i,x i)^2 := by
    have := (mul_eq_zero.mp hQ'.symm).resolve_left hprod.ne'
    exact sub_eq_zero.mp this
  have hc := fourRowMinorant_tangent_cauchy r x hs hx
  have hnonneg : 0 ≤ ∑ i,x i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hzero : (∑ i,x i^2)=0 := by
    rw [← hsq] at hc
    nlinarith
  have hxi (i : Fin 4) : x i=0 := by
    have hi := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4))) => sq_nonneg (x j))
      (Finset.mem_univ i)
    rw [hzero] at hi
    exact sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _))
  rw [← hfactor]
  ext i
  simp [hxi]

theorem fourRowMinorant_gradient_difference_dot (r v w : Fin 4 → ℝ) :
    (∑ i, (fourRowMinorantGradient r (fun j => v j+w j) i-fourRowMinorantGradient r v i)*w i) =
      2*fourRowMinorantQuadratic r w := by
  norm_num [fourRowMinorantGradient, fourRowMinorantQuadratic, fourRow_complement_product,
    Fin.sum_univ_succ, Fin.prod_univ_succ, Finset.sum_erase,
    Fin.ext_iff, -Fin.val_eq_zero_iff]
  ring

/-- The stationary vector is a conclusion of actual constrained minimization, including its feasibility. -/
theorem IsFourRowMinorantMinimum.eq_stationary {r v : Fin 4 → ℝ}
    (hmin : IsFourRowMinorantMinimum r v) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    (hv : ∀ i,0<v i) (hvs : ∑ i,v i=1) : v=fourRowMinorantStationary r := by
  have hq := hmin.squareSum_lt hr hs hv hvs
  have hd : fourRowMinorantDelta r ≠ 0 := by unfold fourRowMinorantDelta; linarith
  let w : Fin 4 → ℝ := fun i => v i-fourRowMinorantStationary r i
  have hws : (∑ i,w i)=0 := by
    simp only [w, Finset.sum_sub_distrib, hvs, fourRowMinorantStationary_sum r hs, sub_self]
  have hg := hmin.gradient_dot_zero hv hvs w hws
  have hgstar : (∑ i,fourRowMinorantGradient r (fourRowMinorantStationary r) i*w i)=0 := by
    simp only [fourRowMinorantStationary_gradient r hs hd, ← Finset.mul_sum, hws, mul_zero]
  have hdiff := fourRowMinorant_gradient_difference_dot r (fourRowMinorantStationary r) w
  have hsum : (fun i => fourRowMinorantStationary r i+w i)=v := by funext i; simp [w]
  rw [hsum] at hdiff
  simp only [sub_mul, Finset.sum_sub_distrib, hg, hgstar, sub_self] at hdiff
  have hQ : fourRowMinorantQuadratic r w=0 := by linarith
  have hwzero := fourRowMinorantQuadratic_tangent_zero r w hr hs hq hws hQ
  funext i
  have hi := congrFun hwzero i
  exact sub_eq_zero.mp hi

end DittertRybin
