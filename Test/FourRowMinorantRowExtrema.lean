import DR.Rectangular.FourRowMinorantRowExtrema

open DittertRybin
open scoped BigOperators

-- Both moments are exact on signed rows and every real curve parameter.
example (r : Fin 4 → ℝ) (t : ℝ) :
    (∑ i,fourRowMinorantRowCurve r t i)=∑ i,r i := fourRowMinorantRowCurve_sum r t

example (r : Fin 4 → ℝ) (t : ℝ) :
    fourRowMinorantSquareSum (fourRowMinorantRowCurve r t)=fourRowMinorantSquareSum r :=
  fourRowMinorantRowCurve_squareSum r t

example : (∏ i,threeMomentCurve ![2,2,1] (1/2) i)-(2:ℝ)^2*1=36/343 := by
  rw [threeMomentCurve_repeated_product_gain]
  norm_num

example (A B : ℝ) : (∏ i,threeMomentCurve ![A,A,B] 1 i)-A^2*B=0 := by
  rw [threeMomentCurve_repeated_product_gain]
  norm_num

example (A B : ℝ) : (∏ i,threeMomentCurve ![A,A,B] (-1) i)-A^2*B=0 := by
  rw [threeMomentCurve_repeated_product_gain]
  norm_num

example : ¬ IsLocalMax (fun t : ℝ => ∏ i,threeMomentCurve ![2,2,1] t i) 0 :=
  threeMomentCurve_not_localMax_repeated_larger (by norm_num)

-- Expanded actual closed fixed-q maximum; the optimizer form is a conclusion.
example (γ : ℝ) (r : Fin 4 → ℝ) (hγ : 0<γ)
    (hr : ∀ i,0<r i) (hs : ∑ i,r i=1) (hv : ∀ i,0<fourRowMinorantStationary r i)
    (hq0 : 1/4<fourRowMinorantSquareSum r) (hq1 : fourRowMinorantSquareSum r<1/3)
    (hmax : ∀ u : Fin 4 → ℝ, (∀ i,0≤u i) → (∑ i,u i)=1 →
      fourRowMinorantSquareSum u=fourRowMinorantSquareSum r →
      (∀ i,0≤fourRowMinorantStationary u i) →
      fourRowMinorantE3 u+γ*(∏ i,u i)≤fourRowMinorantE3 r+γ*(∏ i,r i)) :
    ∃ (R : ℝ) (e : Equiv.Perm (Fin 4)), 1/4<R ∧ R<1/2 ∧
      r ∘ e=fourRowMinorantOneLargeRows R :=
  IsFourRowMinorantRowMaximum.one_large hmax hγ hr hs hv hq0 hq1

#print axioms fourRowMinorantRowCurve_squareSum
#print axioms fourRowMinorantRowCurve_eventually_feasible
#print axioms IsFourRowMinorantRowMaximum.triple_localMax
#print axioms threeMomentCurve_repeated_product_gain
#print axioms IsFourRowMinorantRowMaximum.permute
#print axioms IsFourRowMinorantRowMaximum.one_large
