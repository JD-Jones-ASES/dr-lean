import DR.Endpoint.LeadingConstants
import DR.ElementarySymmetricBoundsVariance

/-! Conversion from the variance of actual leading column costs to column
mass variance. Centering retains the non-unit total of the cost vector. -/
namespace DittertRybin
open scoped BigOperators

noncomputable def centeredVariance {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ j, (x j-(∑ k, x k)/(n:ℝ))^2

theorem centeredVariance_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ centeredVariance x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem centeredVariance_eq_sum_sq {n : ℕ} (hn : 0<n) (x : Fin n → ℝ) :
    centeredVariance x = (∑ j, (x j)^2)-(∑ j, x j)^2/(n:ℝ) := by
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold centeredVariance
  simp_rw [sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ← Finset.sum_mul,← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  ring

theorem centeredVariance_le_sum_sq {n : ℕ} (hn : 0<n) (x : Fin n → ℝ) :
    centeredVariance x ≤ ∑ j, (x j)^2 := by
  rw [centeredVariance_eq_sum_sq hn]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))

theorem centeredVariance_eq_marginalVariance {n : ℕ} (x : Fin n → ℝ)
    (hs : ∑ j, x j=1) : centeredVariance x=marginalVariance x := by
  simp only [centeredVariance,marginalVariance,hs]

theorem centeredVariance_add_le {n : ℕ} (x y : Fin n → ℝ) :
    centeredVariance (fun j => x j+y j) ≤
      2*centeredVariance x+2*centeredVariance y := by
  unfold centeredVariance
  rw [Finset.sum_add_distrib]
  calc
    (∑ j, (x j+y j-((∑ k, x k)+(∑ k, y k))/(n:ℝ))^2) ≤
        ∑ j, (2*(x j-(∑ k, x k)/(n:ℝ))^2+
          2*(y j-(∑ k, y k)/(n:ℝ))^2) := by
      apply Finset.sum_le_sum
      intro j _
      rw [add_div]
      nlinarith only [sq_nonneg ((x j-(∑ k, x k)/(n:ℝ))-
        (y j-(∑ k, y k)/(n:ℝ)))]
    _ = _ := by rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]

/-- A nonnegative mass-one vector and multiplicatively close costs have
comparable centered variances. The cost vector need not have mass one. -/
theorem longColumn_variance_conversion {n : ℕ} (hn : 0<n)
    (c α : Fin n → ℝ) (_hc : ∀ j, 0≤c j) (hs : ∑ j, c j=1)
    {ρ : ℝ} (hρ : 0≤ρ) (hρ8 : ρ<1/8)
    (hl : ∀ j, (1-ρ)*c j≤α j) (hu : ∀ j, α j≤c j) :
    marginalVariance c ≤ 3*centeredVariance α+3*ρ^2/(n:ℝ) := by
  let e := fun j => c j-α j
  have he0 (j) : 0≤e j := sub_nonneg.mpr (hu j)
  have hecap (j) : e j≤ρ*c j := by dsimp [e]; linarith [hl j]
  have heq : (fun j => α j+e j)=c := by funext j; dsimp [e]; ring
  have htri := centeredVariance_add_le α e
  rw [heq,centeredVariance_eq_marginalVariance c hs] at htri
  have hesq : (∑ j, (e j)^2)≤ρ^2*(∑ j, (c j)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := pow_le_pow_left₀ (he0 j) (hecap j) 2
    simpa only [mul_pow] using h
  have hevar := (centeredVariance_le_sum_sq hn e).trans hesq
  have hid := marginalVariance_eq_sum_sq hn hs
  have hV := marginalVariance_nonneg c
  have hW := centeredVariance_nonneg α
  have hρsq : ρ^2≤1/64 := by nlinarith only [hρ,hρ8]
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hi : 0≤1/(n:ℝ) := by positivity
  have hvscale := mul_le_mul_of_nonneg_right hρsq hV
  have hid' : (∑ j, (c j)^2)=marginalVariance c+1/(n:ℝ) := by linarith
  rw [hid'] at hevar
  have hresult : marginalVariance c ≤ 3*centeredVariance α+3*ρ^2*(1/(n:ℝ)) := by
    nlinarith only [htri,hevar,hvscale,hW,hV,mul_nonneg (sq_nonneg ρ) hi]
  convert hresult using 1
  ring

/-- A pointwise column bound from the cost variance, with the actual cost
total used for centering. No normalization of the cost vector is assumed. -/
theorem longColumn_coordinate_sq_le {n : ℕ} (hn : 0<n)
    (c α : Fin n → ℝ) (hc : ∀ j, 0≤c j) (hs : ∑ j, c j=1)
    {ρ : ℝ} (hρ : 0≤ρ) (hρ8 : ρ<1/8)
    (hl : ∀ j, (1-ρ)*c j≤α j) (hu : ∀ j, α j≤c j) (j : Fin n) :
    (c j)^2 ≤ 4/(n:ℝ)^2+4*centeredVariance α := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hd : 0≤1-ρ := by linarith
  have hα (j) : 0≤α j := (mul_nonneg hd (hc j)).trans (hl j)
  have hH0 : 0≤∑ k, α k := Finset.sum_nonneg fun k _ => hα k
  have hH1 : (∑ k, α k)≤1 := by
    simpa only [hs] using Finset.sum_le_sum (fun k (_ : k∈Finset.univ) => hu k)
  have hmean0 : 0≤(∑ k, α k)/(n:ℝ) := div_nonneg hH0 hnR.le
  have hmean1 := div_le_div_of_nonneg_right hH1 hnR.le
  have hmean2 := pow_le_pow_left₀ hmean0 hmean1 2
  have hcenter : (α j-(∑ k, α k)/(n:ℝ))^2≤centeredVariance α := by
    exact Finset.single_le_sum
      (fun k (_ : k∈Finset.univ) => sq_nonneg (α k-(∑ l, α l)/(n:ℝ)))
      (Finset.mem_univ j)
  have hsq := pow_le_pow_left₀ (mul_nonneg hd (hc j)) (hl j) 2
  have hsmall : (1/2:ℝ)≤(1-ρ)^2 := by nlinarith only [hρ,hρ8]
  have hscale := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (c j))
  rw [mul_pow] at hsq
  have hresult : (c j)^2≤4*(1/(n:ℝ))^2+4*centeredVariance α := by
    nlinarith only [hcenter,hmean2,hsq,hscale,
      sq_nonneg (α j-2*((∑ k, α k)/(n:ℝ)))]
  convert hresult using 1
  field_simp

noncomputable def endpointLeadingRho (m : ℕ) : ℝ :=
  1-Real.sqrt (1-endpointLeadingDefect m)

theorem endpointLeadingRho_bounds {m : ℕ} (hm : 5≤m) :
    0≤endpointLeadingRho m ∧ endpointLeadingRho m<1/8 ∧
      endpointLeadingRho m≤5*dittertConstant m := by
  have hb0 := (endpointLeadingDefect_bounds (by omega : 3≤m)).1
  have hb1 := endpointLeadingDefect_le_two_ninths hm
  have ht0 := Real.sqrt_nonneg (1-endpointLeadingDefect m)
  have ht2 := Real.sq_sqrt (show 0≤1-endpointLeadingDefect m by linarith)
  have ht1 : Real.sqrt (1-endpointLeadingDefect m)≤1 := by nlinarith
  have htlo : (7/8:ℝ)<Real.sqrt (1-endpointLeadingDefect m) := by nlinarith
  have hratio := endpointLeadingDefect_lt_alpha_ratio hm
  have hprod := mul_le_mul_of_nonneg_left htlo.le (sub_nonneg.mpr ht1)
  have ha0 := (dittertConstant_pos (by omega : 0<m)).le
  dsimp only [endpointLeadingRho]
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith only [hprod,ht2,hratio,ha0]

theorem endpointLeading_column_costs {m n : ℕ} (hm : 5≤m)
    (P : Board m n) (hP : IsProbability P) (j : Fin n) :
    (1-endpointLeadingRho m)*colSum P j≤endpointLeadingColumnCost P j ∧
      endpointLeadingColumnCost P j≤colSum P j := by
  simpa only [endpointLeadingRho,sub_sub_cancel] using
    endpointLeadingColumnCost_bounds (by omega : 3≤m) P hP j

theorem endpointLeading_variance_conversion {m n : ℕ} (hm : 5≤m) (hn : 0<n)
    (P : Board m n) (hP : IsProbability P) :
    marginalVariance (colSum P) ≤ 3*centeredVariance (endpointLeadingColumnCost P)+
      3*(endpointLeadingRho m)^2/(n:ℝ) := by
  have hr := endpointLeadingRho_bounds hm
  exact longColumn_variance_conversion hn (colSum P) (endpointLeadingColumnCost P)
    (colSum_nonneg hP.1) (by rw [← totalMass_eq_sum_colSum]; exact hP.2)
    hr.1 hr.2.1 (fun j => (endpointLeading_column_costs hm P hP j).1)
    (fun j => (endpointLeading_column_costs hm P hP j).2)

theorem endpointLeading_column_sq_le {m n : ℕ} (hm : 5≤m) (hn : 0<n)
    (P : Board m n) (hP : IsProbability P) (j : Fin n) :
    (colSum P j)^2 ≤ 4/(n:ℝ)^2+4*centeredVariance (endpointLeadingColumnCost P) := by
  have hr := endpointLeadingRho_bounds hm
  exact longColumn_coordinate_sq_le hn (colSum P) (endpointLeadingColumnCost P)
    (colSum_nonneg hP.1) (by rw [← totalMass_eq_sum_colSum]; exact hP.2)
    hr.1 hr.2.1 (fun k => (endpointLeading_column_costs hm P hP k).1)
    (fun k => (endpointLeading_column_costs hm P hP k).2) j

end DittertRybin
