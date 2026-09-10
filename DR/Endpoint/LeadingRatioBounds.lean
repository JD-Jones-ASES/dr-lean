import DR.Endpoint.LeadingMoments

/-! Actual ratio and row-derivative bounds, retaining every empty column. -/
namespace DittertRybin
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def endpointLeadingRatioCap (m : ℕ) : ℝ :=
  1/Real.sqrt (1-endpointLeadingDefect m)

theorem endpointLeadingRowDerivative_bounds {m n : ℕ} (hm : 3≤m)
    (r : Fin m → ℝ) (X : Board m n) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) (i : Fin m) :
    1≤endpointLeadingRowDerivative r X i ∧
      endpointLeadingRowDerivative r X i≤endpointLeadingRatioCap m := by
  have hP := endpointRowBoard_isProbability r X (fun i => (hr i).le) hs hX hXS
  have hb : 0<Real.sqrt (1-endpointLeadingDefect m) :=
    Real.sqrt_pos.mpr (by linarith [(endpointLeadingDefect_bounds hm).2])
  have ht (j : Fin n) : X i j≤X i j*endpointLeadingRatio r X j ∧
      X i j*endpointLeadingRatio r X j≤X i j*endpointLeadingRatioCap m := by
    by_cases hz : X i j=0
    · simp [hz]
    · have hx : 0<X i j := lt_of_le_of_ne (hX i j) (Ne.symm hz)
      have hc : 0<colSum (endpointRowBoard r X) j := (mul_pos (hr i) hx).trans_le
        (Finset.single_le_sum (fun a _ => mul_nonneg (hr a).le (hX a j)) (Finset.mem_univ i))
      have hcost := endpointLeadingColumnCost_pos hm (endpointRowBoard r X) hP j hc
      have hbounds := endpointLeadingColumnCost_bounds hm (endpointRowBoard r X) hP j
      have hl : 1≤endpointLeadingRatio r X j := by
        apply (le_div_iff₀ hcost).mpr
        simpa only [one_mul,colSum,endpointRowBoard] using hbounds.2
      have hu : endpointLeadingRatio r X j≤endpointLeadingRatioCap m := by
        apply (div_le_div_iff₀ hcost hb).mpr
        simpa only [one_mul,mul_one,mul_comm,colSum,endpointRowBoard] using hbounds.1
      exact ⟨by simpa only [mul_one] using mul_le_mul_of_nonneg_left hl (hX i j),
        mul_le_mul_of_nonneg_left hu (hX i j)⟩
  have hl := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => (ht j).1)
  have hu := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => (ht j).2)
  change rowSum X i≤endpointLeadingRowDerivative r X i at hl
  rw [← Finset.sum_mul,show ∑ j,X i j=1 from hXS i,one_mul] at hu
  exact ⟨by simpa only [hXS i] using hl,hu⟩

theorem endpointLeadingMoment_nonneg {m n : ℕ} (r : Fin m → ℝ) (X : Board m n)
    (hr : ∀ i,0≤r i) (hX : ∀ i j,0≤X i j) : 0≤endpointLeadingMoment r X := by
  unfold endpointLeadingMoment
  apply mul_nonneg
  · unfold endpointLeadingScale
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun i _ => hr i))) (by norm_num)
  · apply Finset.sum_nonneg
    intro j hj
    apply div_nonneg
    · exact sub_nonneg.mpr (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hX i j))
    · exact Real.sqrt_nonneg _

theorem endpointLeadingGauge_le_one {m n : ℕ} (hm : 3≤m)
    (P : Board m n) (hP : IsProbability P) : endpointLeadingGauge P≤1 := by
  calc
    _ ≤ ∑ j,colSum P j := Finset.sum_le_sum (fun j _ => (endpointLeadingColumnCost_bounds hm P hP j).2)
    _ = 1 := (totalMass_eq_sum_colSum P).symm.trans hP.2

theorem endpointLeadingGauge_nonneg {m n : ℕ} (P : Board m n) : 0≤endpointLeadingGauge P :=
  Finset.sum_nonneg (fun _j _ => Real.sqrt_nonneg _)

theorem endpointLeadingGauge_pos {m n : ℕ} (hm : 3≤m)
    (r : Fin m → ℝ) (X : Board m n) (hr : ∀ i,0≤r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) :
    0<endpointLeadingGauge (endpointRowBoard r X) := by
  have h := endpointLeading_weighted_cauchy hm r X hr hs hX hXS
  have hn := endpointLeadingGauge_nonneg (endpointRowBoard r X)
  by_contra hg
  have hz : endpointLeadingGauge (endpointRowBoard r X)=0 := le_antisymm (le_of_not_gt hg) hn
  rw [hz,zero_mul] at h
  norm_num at h

end DittertRybin
