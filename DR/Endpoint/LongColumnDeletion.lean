import DR.Endpoint.DeletedRowBalance

/-! An asymmetric centered-deletion estimate for the long-column row budget.
The original and retained row marginals are kept distinct. -/
namespace DittertRybin
open scoped BigOperators

theorem longColumn_deleted_row_sq_scaled_le {m : ℕ} (r tau : Fin m → ℝ) (w : ℝ)
    (htau : ∀ i,0≤tau i) (hs : ∑ i,tau i=w) (hw : w<1) :
    (∑ i,(1-(m:ℝ)*((r i-tau i)/(1-w)))^2)*(1-w)^2≤
      (5/4)*(∑ i,((m:ℝ)*r i-1)^2)+5*(m:ℝ)^2*w^2 := by
  have hh : 0<1-w := by linarith
  have htausq : (∑ i,tau i^2)≤w^2 := by
    simpa only [hs] using Finset.sum_sq_le_sq_sum_of_nonneg
      (s:=Finset.univ) (f:=tau) (fun i _ => htau i)
  have heq : (∑ i,((m:ℝ)*tau i-w)^2)=
      (m:ℝ)^2*(∑ i,tau i^2)-(m:ℝ)*w^2 := by
    simp only [sub_sq,mul_pow,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      ← Finset.mul_sum,← Finset.sum_mul,hs,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul]
    ring
  have hesq : (∑ i,((m:ℝ)*tau i-w)^2)≤(m:ℝ)^2*w^2 := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_left htausq (sq_nonneg (m:ℝ)),
      mul_nonneg (Nat.cast_nonneg m) (sq_nonneg w)]
  have hpoint (i : Fin m) :
      (1-(m:ℝ)*((r i-tau i)/(1-w)))^2*(1-w)^2≤
        (5/4)*((m:ℝ)*r i-1)^2+5*((m:ℝ)*tau i-w)^2 := by
    have hid : (1-(m:ℝ)*((r i-tau i)/(1-w)))*(1-w)=
        -((m:ℝ)*r i-1)+((m:ℝ)*tau i-w) := by field_simp; ring
    rw [← mul_pow,hid]
    nlinarith [sq_nonneg (((m:ℝ)*r i-1)/2+2*((m:ℝ)*tau i-w))]
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
  simp only [← Finset.sum_mul,Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  linarith

theorem longColumn_deleted_row_sq_lt {m : ℕ} (hm : 1≤m)
    (r tau : Fin m → ℝ) (w : ℝ) (htau : ∀ i,0≤tau i)
    (hs : ∑ i,tau i=w) (hw : (m:ℝ)*w≤1/100)
    (hr : (∑ i,((m:ℝ)*r i-1)^2)<1/16) :
    (∑ i,(1-(m:ℝ)*((r i-tau i)/(1-w)))^2)<1/9 := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hw0 : 0≤w := hs ▸ Finset.sum_nonneg (fun i _ => htau i)
  have hw1 : w≤1/100 := by nlinarith
  have hhsq : (9801/10000:ℝ)≤(1-w)^2 := by nlinarith
  have hmwsq : (m:ℝ)^2*w^2≤1/10000 := by
    have hmw0 : 0≤(m:ℝ)*w := by positivity
    nlinarith
  have hsum := longColumn_deleted_row_sq_scaled_le r tau w htau hs (by linarith)
  have hq0 : 0≤∑ i,(1-(m:ℝ)*((r i-tau i)/(1-w)))^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hl := mul_le_mul_of_nonneg_left hhsq hq0
  nlinarith only [hsum,hr,hmwsq,hl]

theorem longColumn_kept_row_sq_lt {m n : ℕ} (hm : 1≤m) {P : Board m n}
    (hP : IsProbability P) (S : Finset (Fin n))
    (hw : (m:ℝ)*(1-totalMass (keepColumns P S))≤1/100)
    (hr : (∑ i,((m:ℝ)*rowSum P i-1)^2)<1/16) :
    (∑ i,(1-(m:ℝ)*(rowSum (keepColumns P S) i/totalMass (keepColumns P S)))^2)<1/9 := by
  let tau : Fin m → ℝ := fun i => rowSum P i-rowSum (keepColumns P S) i
  have htau : ∀ i,0≤tau i := fun i => sub_nonneg.mpr (rowSum_keepColumns_le hP.1 S i)
  have hs : (∑ i,tau i)=1-totalMass (keepColumns P S) := by
    simp only [tau,Finset.sum_sub_distrib]
    change totalMass P-totalMass (keepColumns P S)=_
    rw [hP.2]
  have h := longColumn_deleted_row_sq_lt hm (rowSum P) tau
    (1-totalMass (keepColumns P S)) htau hs hw hr
  simpa only [tau,sub_sub_cancel] using h

end DittertRybin
