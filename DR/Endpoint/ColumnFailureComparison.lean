import DR.Endpoint.ColumnAveraging
import DR.Endpoint.LeadingEvent
import DR.ElementarySymmetricBoundsVariance

/-! Quantitative comparison of actual iid column failure with uniformity.
Exact pair averaging and compact minimum-norm selection prove the same
radial Schur bound, including negative lower coefficients and zero entries. -/
namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def endpointColumnFailure {d : ℕ} (m : ℕ) (x : Fin d → ℝ) : ℝ :=
  1-(m.factorial:ℝ)*elementarySymmetric x m

theorem continuous_endpointColumnFailure (m d : ℕ) :
    Continuous (endpointColumnFailure (d:=d) m) := by
  unfold endpointColumnFailure elementarySymmetric
  fun_prop

theorem endpointColumnMidpoint_elementary {d m : ℕ} (hm : 2≤m) (x : Fin d → ℝ)
    (a b : Fin d) (hab : a≠b) :
    elementarySymmetric (endpointColumnMidpoint x a b) m-elementarySymmetric x m=
      (1/4:ℝ)*(x a-x b)^2*
        elementarySymmetric (fun i => if i∈({a,b}:Finset (Fin d)) then 0 else x i) (m-2) := by
  classical
  let P : Board 1 d := fun _ => x
  have hc : colSum P=x := by ext i; simp [colSum,P]
  have hmid : colSum (blendColumns P a b (1/2))=endpointColumnMidpoint x a b := by
    ext i
    simp only [colSum,Fin.sum_univ_one,P,blendColumns,endpointColumnMidpoint]
    split_ifs <;> ring
  have he := elementary_blend_difference (k:=m-2) P a b hab (1/2)
  rw [Nat.sub_add_cancel hm,hmid,hc] at he
  have hdel : colSum (eraseColumns P {a,b})=
      fun i => if i∈({a,b}:Finset (Fin d)) then 0 else x i := by
    ext i
    rw [colSum_eraseColumns,hc]
  simpa only [averagingCoefficient,hdel,show (1/2:ℝ)*(1-1/2)=1/4 by norm_num] using he

theorem endpointColumnMidpoint_adjusted_failure_le {d m : ℕ} (hm : 2≤m)
    (x : Fin d → ℝ) {C : ℝ} (hx : x∈endpointCappedSimplex d C)
    (a b : Fin d) (hab : a≠b) :
    endpointColumnFailure m (endpointColumnMidpoint x a b)-
      (m.choose 2:ℝ)*(1-((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)*C/2)*
        (∑ i,(endpointColumnMidpoint x a b i)^2)≤
    endpointColumnFailure m x-
      (m.choose 2:ℝ)*(1-((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)*C/2)*(∑ i,(x i)^2) := by
  classical
  let E := elementarySymmetric (fun i => if i∈({a,b}:Finset (Fin d)) then 0 else x i) (m-2)
  let B := 1-((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)*C/2
  have he := endpointColumnMidpoint_elementary hm x a b hab
  have hlow := endpoint_deleted_elementary_lower (k:=m-2) x (fun i => (hx.1 i).1)
    hx.2 ((hx.1 a).1.trans (hx.1 a).2) (fun i => (hx.1 i).2) a b hab
  have hlow' : B≤((m-2).factorial:ℝ)*E := by
    dsimp [B,E]
    nlinarith only [hlow]
  have hmul := mul_le_mul_of_nonneg_left hlow'
    (show 0≤(m.choose 2:ℝ)*2 by positivity)
  have hf := endpoint_choose_two_factorial hm
  have hcoef : 0≤(m.factorial:ℝ)*E-2*(m.choose 2:ℝ)*B := by
    have hid : (m.choose 2:ℝ)*2*((m-2).factorial:ℝ)*E=(m.factorial:ℝ)*E := by rw [hf]
    nlinarith only [hmul,hid]
  have hgain := mul_nonneg (sq_nonneg (x a-x b)) hcoef
  have he' := congrArg (fun t : ℝ => (m.factorial:ℝ)*t) he
  change (m.factorial:ℝ)*(elementarySymmetric (endpointColumnMidpoint x a b) m-
    elementarySymmetric x m)=(m.factorial:ℝ)*((1/4:ℝ)*(x a-x b)^2*E) at he'
  change endpointColumnFailure m (endpointColumnMidpoint x a b)-
    (m.choose 2:ℝ)*B*(∑ i,(endpointColumnMidpoint x a b i)^2)≤
    endpointColumnFailure m x-(m.choose 2:ℝ)*B*(∑ i,(x i)^2)
  rw [endpointColumnMidpoint_square x a b hab]
  unfold endpointColumnFailure
  nlinarith only [he',hgain]

theorem endpointColumnFailure_uniform {d : ℕ} (_hd : 0<d) (m : ℕ) :
    endpointColumnFailure m (fun _ : Fin d => 1/(d:ℝ))=1-distinctUniformProbability d m := by
  rw [endpointColumnFailure,elementarySymmetric_const]
  simp only [distinctUniformProbability,Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul,
    div_pow,one_pow]
  ring

/-- The retained-uniform Schur bound, derived from actual coefficient averaging. -/
theorem endpoint_column_failure_comparison {d m : ℕ} (hd : 0<d) (hm : 2≤m)
    (x : Fin d → ℝ) (hx : ∀ i,0≤x i) (hs : ∑ i,x i=1)
    (C : ℝ) (hC : ∀ i,x i≤C) :
    (m.choose 2:ℝ)*(1-((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)*C/2)*marginalVariance x≤
      endpointColumnFailure m x-(1-distinctUniformProbability d m) := by
  let B := 1-((m-2:ℕ):ℝ)*(((m-2:ℕ):ℝ)+3)*C/2
  let F : (Fin d → ℝ) → ℝ := fun y => endpointColumnFailure m y-(m.choose 2:ℝ)*B*(∑ i,(y i)^2)
  have hF : Continuous F := (continuous_endpointColumnFailure m d).sub (by fun_prop)
  have hmid : ∀ y∈endpointCappedSimplex d C,∀ a b : Fin d,a≠b→
      F (endpointColumnMidpoint y a b)≤F y := by
    intro y hy a b hab
    exact endpointColumnMidpoint_adjusted_failure_le hm y hy a b hab
  have h := endpoint_midpoint_uniform_comparison hd C F hF hmid x ⟨fun i => ⟨hx i,hC i⟩,hs⟩
  have hu : (∑ _i : Fin d,(1/(d:ℝ))^2)=1/(d:ℝ) := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hdR : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
    field_simp
  dsimp [F] at h
  rw [endpointColumnFailure_uniform hd m,hu] at h
  rw [marginalVariance_eq_sum_sq hd hs]
  change (m.choose 2:ℝ)*B*((∑ i,(x i)^2)-1/(d:ℝ))≤_
  linarith

end DittertRybin
