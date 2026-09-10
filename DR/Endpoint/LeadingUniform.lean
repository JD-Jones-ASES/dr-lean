import DR.Endpoint.LeadingBoundary

/-! The exact uniform leading-gauge value and full-minimum comparison. -/
namespace DittertRybin
open scoped BigOperators
open Certificates

/-- Exact scaling of an arbitrary real quadratic form. -/
theorem endpoint_quadratic_scale {ι : Type*} [Fintype ι] (Q : Matrix ι ι ℝ)
    (x : ι → ℝ) (c : ℝ) : quadraticValue Q (fun i => c*x i)=c^2*quadraticValue Q x := by
  unfold quadraticValue
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem endpoint_leading_factorial_two {m : ℕ} (hm : 2≤m) :
    (m.factorial:ℝ)=((m-2).factorial:ℝ)*(m:ℝ)*((m:ℝ)-1) := by
  have hf := Nat.factorial_mul_descFactorial (n:=m) (k:=2) hm
  have hcast := congrArg (fun q : ℕ => (q:ℝ)) hf
  simp only [Nat.cast_mul,Nat.descFactorial_succ,Nat.descFactorial_zero,
    Nat.cast_sub (by omega : 1≤m),Nat.cast_one,Nat.sub_zero,mul_one] at hcast
  nlinarith only [hcast]

/-- The exact marginal quadratic, retaining all signed and zero rows. -/
theorem endpointLeadingKernel_marginal_value {m : ℕ} (hm : 2≤m) (r : Fin m → ℝ) :
    quadraticValue (endpointLeadingKernel r) r=(∑ i,r i)^2-(m.factorial:ℝ)*∏ i,r i := by
  have h := endpointLeadingKernel_scaled_quadratic r (fun _ => 1)
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at h
  have hf := congrArg (fun a : ℝ => a*∏ i,r i) (endpoint_leading_factorial_two hm)
  unfold endpointLeadingScale at h
  nlinarith only [h,hf]

theorem endpoint_uniform_row_marginal {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    rowSum (uniformBoard m n)=fun _ => 1/(m:ℝ) := by
  funext i
  simp only [rowSum,uniformBoard,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hmR : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp

theorem endpoint_uniform_row_square {m n : ℕ} (hm : 0<m) (hn : 0<n) :
    (∑ i,(rowSum (uniformBoard m n) i)^2)=1/(m:ℝ) := by
  rw [endpoint_uniform_row_marginal hm hn]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have hmR : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  field_simp

theorem endpointLeadingColumnCost_uniform {m n : ℕ} (hm : 2≤m) (hn : 0<n) (j : Fin n) :
    endpointLeadingColumnCost (uniformBoard m n) j=
      (1/(n:ℝ))*Real.sqrt (1-dittertConstant m) := by
  have hm0 : 0<m := by omega
  have hmR : (m:ℝ)≠0 := by exact_mod_cast hm0.ne'
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  have hcol : (fun i : Fin m => uniformBoard m n i j)=fun _ => (1/(n:ℝ))*(1/(m:ℝ)) := by
    funext i
    unfold uniformBoard
    field_simp
  have hq : quadraticValue (endpointLeadingKernel (fun _ : Fin m => 1/(m:ℝ)))
      (fun _ => 1/(m:ℝ))=1-dittertConstant m := by
    rw [endpointLeadingKernel_marginal_value hm]
    simp only [Finset.sum_const,Finset.prod_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    unfold dittertConstant
    simp [hmR,div_eq_mul_inv]
  unfold endpointLeadingColumnCost
  rw [endpoint_uniform_row_marginal hm0 hn,hcol,endpoint_quadratic_scale,hq,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (by positivity : (0:ℝ)≤1/(n:ℝ))]

theorem endpointLeadingGauge_uniform {m n : ℕ} (hm : 2≤m) (hn : 0<n) :
    endpointLeadingGauge (uniformBoard m n)=Real.sqrt (1-dittertConstant m) := by
  unfold endpointLeadingGauge
  simp only [endpointLeadingColumnCost_uniform hm hn,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul]
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp

theorem IsEndpointGaugeMinimum.le_uniform {m n : ℕ} (hm : 2≤m) (hn : 0<n)
    {P : Board m n} {psi : ℝ → ℝ} (hmin : IsEndpointGaugeMinimum P psi) :
    endpointLeadingGauge P-psi (∑ i,(rowSum P i)^2)≤
      Real.sqrt (1-dittertConstant m)-psi (1/(m:ℝ)) := by
  have h := hmin.2 _ (uniformBoard_isProbability (by omega) hn)
  simpa only [endpointLeadingGauge_uniform hm hn,endpoint_uniform_row_square (m:=m) (n:=n) (by omega) hn] using h

/-- AM--GM bounds the leading product scale with its exact factorial normalization. -/
theorem endpointLeadingScale_le {m : ℕ} (hm : 2≤m) (r : Fin m → ℝ)
    (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1) :
    endpointLeadingScale r≤dittertConstant m/((m:ℝ)*((m:ℝ)-1)) := by
  have hmR : (2:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (m:ℝ)≠0 := by linarith
  have hm1 : (m:ℝ)-1≠0 := by linarith
  have h := endpoint_finset_prod_le_mean_pow Finset.univ r
    (by simp; omega) (fun i _ => hr i)
  simp only [Finset.card_univ,Fintype.card_fin,hs,div_pow,one_pow] at h
  have he : dittertConstant m/((m:ℝ)*((m:ℝ)-1))=((m-2).factorial:ℝ)/(m:ℝ)^m := by
    rw [dittertConstant,endpoint_leading_factorial_two hm]
    field_simp
  rw [he]
  have hp := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg (m-2).factorial : (0:ℝ)≤_)
  simpa only [endpointLeadingScale,mul_one_div] using hp

end DittertRybin
