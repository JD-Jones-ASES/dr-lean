import DR.Endpoint.RowProductConcentration
import DR.Collision.Deletion

/-! Closed-domain row balance after deleting a small nonnegative mass.
The squared estimate uses the exact centered deletion vector; it assumes
neither positive entries nor an already-normalized deleted row law. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_deleted_row_sq_lt {m : ℕ} (hm : 1≤m)
    (r tau : Fin m → ℝ) (w : ℝ) (htau : ∀ i,0≤tau i)
    (hs : ∑ i,tau i=w) (hw : (m:ℝ)*w≤1/16)
    (hr : (∑ i,((m:ℝ)*r i-1)^2)<1/1024) :
    (∑ i,(1-(m:ℝ)*((r i-tau i)/(1-w)))^2)<1/81 := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hw0 : 0≤w := hs ▸ Finset.sum_nonneg (fun i _ => htau i)
  have hw1 : w≤1/16 := by nlinarith
  have hh : 0<1-w := by linarith
  have hhsq : (225/256:ℝ)≤(1-w)^2 := by nlinarith
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
    nlinarith [mul_le_mul_of_nonneg_left htausq (sq_nonneg (m:ℝ))]
  have hmwsq : (m:ℝ)^2*w^2≤1/256 := by
    have hmw0 : 0≤(m:ℝ)*w := by positivity
    nlinarith
  have hpoint (i : Fin m) :
      (1-(m:ℝ)*((r i-tau i)/(1-w)))^2*(1-w)^2 ≤
        2*((m:ℝ)*r i-1)^2+2*((m:ℝ)*tau i-w)^2 := by
    have hid : (1-(m:ℝ)*((r i-tau i)/(1-w)))*(1-w)=
        -((m:ℝ)*r i-1)+((m:ℝ)*tau i-w) := by field_simp; ring
    rw [← mul_pow,hid]
    nlinarith [sq_nonneg (((m:ℝ)*r i-1)+((m:ℝ)*tau i-w))]
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hpoint i)
  simp only [← Finset.sum_mul,Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  have hq0 : 0≤∑ i,(1-(m:ℝ)*((r i-tau i)/(1-w)))^2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hl := mul_le_mul_of_nonneg_left hhsq hq0
  nlinarith only [hsum,hr,hesq,hmwsq,hl]

theorem endpoint_kept_row_sq_lt {m n : ℕ} (hm : 1≤m) {P : Board m n}
    (hP : IsProbability P) (S : Finset (Fin n))
    (hw : (m:ℝ)*(1-totalMass (keepColumns P S))≤1/16)
    (hr : (∑ i,((m:ℝ)*rowSum P i-1)^2)<1/1024) :
    (∑ i,(1-(m:ℝ)*(rowSum (keepColumns P S) i/totalMass (keepColumns P S)))^2)<1/81 := by
  let tau : Fin m → ℝ := fun i => rowSum P i-rowSum (keepColumns P S) i
  have htau : ∀ i,0≤tau i := fun i => sub_nonneg.mpr (rowSum_keepColumns_le hP.1 S i)
  have hs : (∑ i,tau i)=1-totalMass (keepColumns P S) := by
    simp only [tau,Finset.sum_sub_distrib]
    change totalMass P-totalMass (keepColumns P S)=_
    rw [hP.2]
  have h := endpoint_deleted_row_sq_lt hm (rowSum P) tau
    (1-totalMass (keepColumns P S)) htau hs hw hr
  simpa only [tau,sub_sub_cancel] using h

theorem endpoint_row_lower_of_sq {m : ℕ} (hm : 0<m) (s : Fin m → ℝ)
    (hs : (∑ i,(1-(m:ℝ)*s i)^2)<1/9) (i : Fin m) :
    (2/3:ℝ)/(m:ℝ)<s i := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have hi := (Finset.single_le_sum (fun j _ => sq_nonneg (1-(m:ℝ)*s j))
    (Finset.mem_univ i)).trans_lt hs
  apply (div_lt_iff₀ hmR).mpr
  nlinarith [sq_nonneg ((m:ℝ)*s i-1/3)]

end DittertRybin
