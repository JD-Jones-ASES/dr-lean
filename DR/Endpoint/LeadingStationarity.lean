import DR.Endpoint.LeadingRows

/-!
# Actual row derivatives of the leading gauge

The ratio and collision moment below are evaluated on one fixed normalized
row law. Empty columns use totalized real division and contribute exactly
zero; their cost function is identically zero under all row scalings.
-/
namespace DittertRybin
open scoped BigOperators Topology
open Certificates Filter
set_option backward.isDefEq.respectTransparency false

noncomputable def endpointLeadingRatio {m n : ℕ} (r : Fin m → ℝ) (X : Board m n)
    (j : Fin n) : ℝ :=
  (∑ i,r i*X i j)/endpointLeadingColumnCost (endpointRowBoard r X) j

noncomputable def endpointLeadingMoment {m n : ℕ} (r : Fin m → ℝ) (X : Board m n) : ℝ :=
  (endpointLeadingScale r/2)*∑ j,
    endpointLeadingColumnCollision X j/endpointLeadingColumnCost (endpointRowBoard r X) j

noncomputable def endpointLeadingRowDerivative {m n : ℕ} (r : Fin m → ℝ)
    (X : Board m n) (i : Fin m) : ℝ :=
  ∑ j,X i j*endpointLeadingRatio r X j

theorem endpointRowBoard_isProbability {m n : ℕ} (r : Fin m → ℝ) (X : Board m n)
    (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1) (hX : ∀ i j,0≤X i j)
    (hXS : ∀ i,rowSum X i=1) : IsProbability (endpointRowBoard r X) := by
  refine ⟨fun i j => mul_nonneg (hr i) (hX i j), ?_⟩
  rw [totalMass_endpointRowBoard r X hXS,hs]

/-- The full column derivative includes every empty column without a
smoothness assumption at sqrt(0). -/
theorem hasDerivAt_endpointLeadingColumnCost_full {m n : ℕ} (hm : 3≤m)
    (r w : Fin m → ℝ) (X : Board m n) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) (j : Fin n) :
    HasDerivAt (fun t : ℝ => endpointLeadingColumnCost
      (endpointRowBoard (fun i => r i+t*w i) X) j)
      (endpointLeadingRatio r X j*(∑ i,w i*X i j)-
        (endpointLeadingScale r/2)*
          (endpointLeadingColumnCollision X j/endpointLeadingColumnCost (endpointRowBoard r X) j)*
          (∑ i,w i/r i)) 0 := by
  classical
  by_cases hj : ∀ i,X i j=0
  · have hfun : (fun t : ℝ => endpointLeadingColumnCost
        (endpointRowBoard (fun i => r i+t*w i) X) j)=fun _ => 0 := by
      funext t
      exact endpointLeadingColumnCost_zero_column _ X j hj
    rw [hfun]
    simp only [endpointLeadingRatio,endpointLeadingColumnCollision,hj,mul_zero,
      Finset.sum_const_zero,zero_pow (by decide : 2≠0),sub_zero,zero_div,mul_zero,zero_mul]
    exact hasDerivAt_const 0 0
  · obtain ⟨i,hi⟩ := not_forall.mp hj
    have hi0 : 0<X i j := lt_of_le_of_ne (hX i j) (Ne.symm hi)
    have hP := endpointRowBoard_isProbability r X (fun i => (hr i).le) hs hX hXS
    have hc : 0<colSum (endpointRowBoard r X) j :=
      (mul_pos (hr i) hi0).trans_le
        (Finset.single_le_sum (fun i _ => mul_nonneg (hr i).le (hX i j)) (Finset.mem_univ i))
    have hcpos := endpointLeadingColumnCost_pos hm (endpointRowBoard r X) hP j hc
    have hq : 0<quadraticValue (endpointLeadingKernel r) (fun i => r i*X i j) := by
      have h := Real.sqrt_pos.mp hcpos
      simpa only [rowSum_endpointRowBoard r X hXS,endpointRowBoard] using h
    have hd := hasDerivAt_endpointLeadingColumnCost r w X hXS (fun i => (hr i).ne') j hq
    convert hd using 1
    unfold endpointLeadingRatio
    field_simp [hcpos.ne']

private theorem leading_derivative_sum {m n : ℕ} (r w : Fin m → ℝ) (X : Board m n) :
    (∑ j : Fin n, (endpointLeadingRatio r X j*(∑ i,w i*X i j)-
      (endpointLeadingScale r/2)*
        (endpointLeadingColumnCollision X j/endpointLeadingColumnCost (endpointRowBoard r X) j)*
        (∑ i,w i/r i)))=
      ∑ i,(endpointLeadingRowDerivative r X i-endpointLeadingMoment r X/r i)*w i := by
  have hfirst : (∑ j : Fin n,endpointLeadingRatio r X j*(∑ i,w i*X i j))=
      ∑ i,endpointLeadingRowDerivative r X i*w i := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [endpointLeadingRowDerivative,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp only [Finset.sum_sub_distrib]
  rw [hfirst]
  have hsecond : (∑ j : Fin n,(endpointLeadingScale r/2)*
      (endpointLeadingColumnCollision X j/endpointLeadingColumnCost (endpointRowBoard r X) j)*
      (∑ i,w i/r i))=∑ i,(endpointLeadingMoment r X/r i)*w i := by
    rw [← Finset.sum_mul,← Finset.mul_sum]
    change endpointLeadingMoment r X*(∑ i,w i/r i)=_
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hsecond]
  simp only [sub_mul,Finset.sum_sub_distrib]

/-- Actual leading-gauge derivative along any real row direction. -/
theorem hasDerivAt_endpointLeadingGauge_line {m n : ℕ} (hm : 3≤m)
    (r w : Fin m → ℝ) (X : Board m n) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) :
    HasDerivAt (fun t : ℝ => endpointLeadingGauge (endpointRowBoard (fun i => r i+t*w i) X))
      (∑ i,(endpointLeadingRowDerivative r X i-endpointLeadingMoment r X/r i)*w i) 0 := by
  have h := HasDerivAt.fun_sum (u:=Finset.univ) (fun j _ =>
    hasDerivAt_endpointLeadingColumnCost_full hm r w X hr hs hX hXS j)
  rw [leading_derivative_sum] at h
  exact h

/-- A true minimum within the feasible row-mass simplex for a fixed law.
An actual minimum over all probability boards supplies this premise by
restriction; the derivative conclusion is not an assumption. -/
def IsEndpointRowGaugeMinimum {m n : ℕ} (r : Fin m → ℝ) (X : Board m n)
    (psi : ℝ → ℝ) : Prop :=
  ∀ s : Fin m → ℝ, (∀ i,0≤s i) → (∑ i,s i)=1 →
    endpointLeadingGauge (endpointRowBoard r X)-psi (∑ i,r i^2) ≤
      endpointLeadingGauge (endpointRowBoard s X)-psi (∑ i,s i^2)

theorem IsEndpointRowGaugeMinimum.line_localMin {m n : ℕ} {r : Fin m → ℝ}
    {X : Board m n} {psi : ℝ → ℝ} (hmin : IsEndpointRowGaugeMinimum r X psi)
    (hr : ∀ i,0<r i) (hs : ∑ i,r i=1) (w : Fin m → ℝ) (hw : ∑ i,w i=0) :
    IsLocalMin (fun t : ℝ => endpointLeadingGauge (endpointRowBoard (fun i => r i+t*w i) X)-
      psi (∑ i,(r i+t*w i)^2)) 0 := by
  have hp : ∀ᶠ t : ℝ in 𝓝 0, ∀ i,0<r i+t*w i := by
    rw [Filter.eventually_all]
    intro i
    exact (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) 0).eventually_lt
      (by fun_prop) (by simpa using hr i)
  filter_upwards [hp] with t ht
  simpa only [zero_mul,add_zero] using hmin (fun i => r i+t*w i) (fun i => (ht i).le)
    (by simp only [Finset.sum_add_distrib,← Finset.mul_sum,hs,hw,mul_zero,add_zero])

/-- Every feasible tangent direction has zero derivative at the actual
penalized minimum. The penalty may be linear or saturated. -/
theorem IsEndpointRowGaugeMinimum.gradient_dot_zero {m n : ℕ} (hm : 3≤m)
    {r : Fin m → ℝ} {X : Board m n} {psi : ℝ → ℝ}
    (hmin : IsEndpointRowGaugeMinimum r X psi) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) (tau : ℝ)
    (hpsi : HasDerivAt psi tau (∑ i,r i^2)) (w : Fin m → ℝ) (hw : ∑ i,w i=0) :
    (∑ i,(endpointLeadingRowDerivative r X i-endpointLeadingMoment r X/r i-2*tau*r i)*w i)=0 := by
  have hq : HasDerivAt (fun t : ℝ => ∑ i,(r i+t*w i)^2) (2*∑ i,r i*w i) 0 := by
    have h := HasDerivAt.fun_sum (u:=Finset.univ) (fun i _ =>
      (((hasDerivAt_id (0:ℝ)).mul_const (w i)).const_add (r i)).pow 2)
    convert! h using 1
    simp only [id_eq,zero_mul,add_zero,Nat.cast_ofNat,Nat.reduceSub,pow_one,one_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hpsi' : HasDerivAt psi tau (∑ i,(r i+0*w i)^2) := by
    simpa only [zero_mul,add_zero] using hpsi
  have hpen := hpsi'.comp 0 hq
  have hd := (hasDerivAt_endpointLeadingGauge_line hm r w X hr hs hX hXS).sub hpen
  have hz := (hmin.line_localMin hr hs w hw).hasDerivAt_eq_zero hd
  have he : (∑ i,(endpointLeadingRowDerivative r X i-endpointLeadingMoment r X/r i-2*tau*r i)*w i)=
      (∑ i,(endpointLeadingRowDerivative r X i-endpointLeadingMoment r X/r i)*w i)-
      tau*(2*∑ i,r i*w i) := by
    simp only [sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]
  exact hz

/-- The common row multiplier is derived using actual pair directions. -/
theorem IsEndpointRowGaugeMinimum.row_gradient_eq {m n : ℕ} (hm : 3≤m)
    {r : Fin m → ℝ} {X : Board m n} {psi : ℝ → ℝ}
    (hmin : IsEndpointRowGaugeMinimum r X psi) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) (tau : ℝ)
    (hpsi : HasDerivAt psi tau (∑ i,r i^2)) (i h : Fin m) :
    endpointLeadingRowDerivative r X i-endpointLeadingMoment r X/r i-2*tau*r i=
      endpointLeadingRowDerivative r X h-endpointLeadingMoment r X/r h-2*tau*r h := by
  classical
  let w : Fin m → ℝ := fun a => (if a=i then 1 else 0)-(if a=h then 1 else 0)
  have hw : (∑ a,w a)=0 := by simp [w,Finset.sum_sub_distrib]
  have hz := hmin.gradient_dot_zero hm hr hs hX hXS tau hpsi w hw
  simp only [w,mul_sub,mul_ite,mul_one,mul_zero,Finset.sum_sub_distrib,
    Finset.sum_ite_eq',Finset.mem_univ,if_true] at hz
  exact sub_eq_zero.mp hz

end DittertRybin
