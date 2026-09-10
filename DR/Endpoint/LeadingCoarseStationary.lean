import DR.Endpoint.LeadingCoarseScalars
import DR.Endpoint.LeadingKernel

/-! Actual stationary scalar data imply positive definiteness of the
original leading kernel for every m>=5. The row interval is derived from
the common gradient and weighted-moment inequality; it is not assumed. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_coarse_stationary_square_bound {m : ℕ} (hm : 5≤m)
    (r A : Fin m → ℝ) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    {a G D C : ℝ} (ha : 0<a) (haU : a≤24/625) (hG : 0<G)
    (hcap : G≤Real.sqrt (1-a)+a/1000) (hCS : 1≤G*(G+2*D))
    (hC : C-1<(1332/275:ℝ)*a) (hA : ∀ i,1≤A i ∧ A i≤C)
    (hstationary : ∀ i,A i=G-((m:ℝ)-2)*D+
      2*(a/1000)*(r i-(∑ j,(r j)^2))+D/r i) :
    (∑ i,(r i)^2)<1/(m:ℝ)+(601/625)/((m:ℝ)*((m:ℝ)-1)) := by
  let tau := a/1000
  let H := 1-G-2*tau
  let k := (m:ℝ)-2
  let d := D/H
  let T := (C-G+2*tau)/H
  have hmR : (5:ℝ)≤m := by exact_mod_cast hm
  have hk : 0<k := by dsimp [k]; linarith
  have htau : 0<tau := by dsimp [tau]; positivity
  have hsqrt := endpoint_coarse_sqrt_cap ha haU
  have hG1 : G<1 := hcap.trans_lt hsqrt.2
  have hHlo : (497/1000:ℝ)*a≤H := by dsimp [H,tau]; linarith only [hcap,hsqrt.1]
  have hH : 0<H := lt_of_lt_of_le (by positivity) hHlo
  have hDgap : 1-G<D := by
    have hg : 0<(1-G)^2 := sq_pos_of_pos (sub_pos.mpr hG1)
    nlinarith only [hCS,hg,hG]
  have hD : 0<D := lt_trans (sub_pos.mpr hG1) hDgap
  have hd : 1<d := by
    apply (lt_div_iff₀ hH).mpr
    dsimp [H,tau]
    linarith only [hDgap,ha]
  have hC1 : 1≤C := (hA ⟨0,by omega⟩).1.trans (hA ⟨0,by omega⟩).2
  have hCg : 0<C-G+2*tau := by linarith only [hC1,hG1,htau]
  have hT : 0<T := div_pos hCg hH
  have hT11 : T<11 := by
    apply (div_lt_iff₀ hH).mpr
    dsimp [H,tau] at hHlo ⊢
    nlinarith only [hHlo,hC,ha]
  have hr1 (i) : r i≤1 := by
    simpa only [hs] using Finset.single_le_sum (fun j (_ : j∈Finset.univ) => (hr j).le)
      (Finset.mem_univ i)
  have hq0 : 0≤∑ i,(r i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq1 : (∑ i,(r i)^2)≤1 := by
    rw [← hs]
    exact Finset.sum_le_sum fun i _ => by nlinarith only [hr i,hr1 i]
  have hpert (i) : -2*tau≤2*tau*(r i-(∑ j,(r j)^2)) ∧
      2*tau*(r i-(∑ j,(r j)^2))≤2*tau := by
    constructor <;> nlinarith only [hr i,hr1 i,hq0,hq1,htau]
  have hlow (i) : d/(T+k*d)≤r i := by
    have hf : 0<C-G+2*tau+k*D := by positivity
    have hh : D/r i≤C-G+2*tau+k*D := by
      have hst := hstationary i
      change A i=G-k*D+2*tau*(r i-(∑ j,(r j)^2))+D/r i at hst
      linarith only [hst,(hA i).2,(hpert i).1]
    have hm := (div_le_iff₀ (hr i)).mp hh
    have hdiv : D/(C-G+2*tau+k*D)≤r i := (div_le_iff₀ hf).mpr (by nlinarith only [hm])
    have he : d/(T+k*d)=D/(C-G+2*tau+k*D) := by
      dsimp [d,T]
      field_simp
    rw [he]
    exact hdiv
  have hupp (i) : r i≤d/(1+k*d) := by
    have hf : 0<H+k*D := by positivity
    have hh : H+k*D≤D/r i := by
      have hst := hstationary i
      change A i=G-k*D+2*tau*(r i-(∑ j,(r j)^2))+D/r i at hst
      dsimp [H]
      linarith only [hst,(hA i).1,(hpert i).2]
    have hm := (le_div_iff₀ (hr i)).mp hh
    have hdiv : r i≤D/(H+k*D) := (le_div_iff₀ hf).mpr (by nlinarith only [hm])
    have he : d/(1+k*d)=D/(H+k*D) := by
      dsimp [d]
      field_simp
    rw [he]
    exact hdiv
  exact endpoint_coarse_rows_square_bound hm r hs hd hT hT11.le hlow hupp

theorem endpoint_coarse_stationary_kernel {m : ℕ} (hm : 5≤m)
    (r A : Fin m → ℝ) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    {a G D C : ℝ} (ha : 0<a) (haU : a≤24/625) (hG : 0<G)
    (hcap : G≤Real.sqrt (1-a)+a/1000) (hCS : 1≤G*(G+2*D))
    (hC : C-1<(1332/275:ℝ)*a) (hA : ∀ i,1≤A i ∧ A i≤C)
    (hstationary : ∀ i,A i=G-((m:ℝ)-2)*D+
      2*(a/1000)*(r i-(∑ j,(r j)^2))+D/r i)
    (hscale : endpointLeadingScale r≤a/((m:ℝ)*((m:ℝ)-1))) :
    (endpointLeadingKernel r).PosDef := by
  have hq := endpoint_coarse_stationary_square_bound hm r A hr hs ha haU hG hcap hCS hC hA hstationary
  have hmR : (5:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hm1 : (0:ℝ)<(m:ℝ)-1 := by linarith
  have hsmall := div_le_div_of_nonneg_right (show (601/625:ℝ)+a≤1 by linarith) (by positivity : 0≤(m:ℝ)*((m:ℝ)-1))
  have he : 1/(m:ℝ)+1/((m:ℝ)*((m:ℝ)-1))=1/((m:ℝ)-1) := by field_simp; ring
  have hh : (∑ i,(r i)^2)+endpointLeadingScale r<1/((m:ℝ)-1) := by
    rw [add_div] at hsmall
    rw [← he]
    linarith only [hq,hscale,hsmall]
  apply endpointLeadingKernel_posDef r hr hs
  have hp := (lt_div_iff₀ hm1).mp hh
  nlinarith only [hp]

end DittertRybin
