import DR.Endpoint.LeadingConstants
import DR.ElementarySymmetricBoundsVariance

/-! Exact scalar interval argument for the all-m>=5 leading gauge.
Source: Analytic-Lab P0174 ENDPOINT_LEADING_GLOBAL.md, sections 3 and 5.
The shifted cubic proves the discriminant sign for every real k>=3,
without finite sampling or a premise asserting kernel positivity. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_coarse_sqrt_cap {a : ℝ} (ha : 0<a) (haU : a≤24/625) :
    Real.sqrt (1-a)≤1-a/2 ∧ Real.sqrt (1-a)+a/1000<1 := by
  have hs := Real.sq_sqrt (show 0≤1-a by linarith)
  have hn := Real.sqrt_nonneg (1-a)
  have hpos : 0≤1-a/2 := by linarith
  have hcap : Real.sqrt (1-a)≤1-a/2 := by
    nlinarith only [hs,hn,hpos,sq_nonneg a]
  exact ⟨hcap,by linarith⟩

theorem endpoint_coarse_interval_discriminant {k : ℝ} (hk : 3≤k) (d : ℝ) :
    (601/625:ℝ)*(1+k*d)*(11+k*d)-(k+1)*(2*d-1)*(11-2*d)>0 := by
  let A : ℝ := (601/625)*k^2+4*(k+1)
  let B : ℝ := 24*(k+1)-12*(601/625)*k
  let C : ℝ := 11*((601/625)+k+1)
  have hA : 0<A := by dsimp [A]; nlinarith only [hk,sq_nonneg k]
  have ht : 0≤k-3 := by linarith
  have hc : 0<165275*k^3+405174*k^2-300300*k-901400 := by
    have hid : 165275*k^3+405174*k^2-300300*k-901400=
        165275*(k-3)^3+1892649*(k-3)^2+6593169*(k-3)+6306691 := by ring
    rw [hid]
    positivity
  have hd : 0<4*A*C-B^2 := by
    have hid : 4*A*C-B^2=4*(165275*k^3+405174*k^2-300300*k-901400)/15625 := by
      dsimp [A,B,C]
      ring
    rw [hid]
    positivity
  have he : 4*A*((601/625:ℝ)*(1+k*d)*(11+k*d)-(k+1)*(2*d-1)*(11-2*d))=
      (2*A*d-B)^2+(4*A*C-B^2) := by dsimp [A,B,C]; ring
  have hp : 0<4*A*((601/625:ℝ)*(1+k*d)*(11+k*d)-(k+1)*(2*d-1)*(11-2*d)) := by
    rw [he]
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) hd
  exact (mul_pos_iff.mp hp).resolve_right (by intro h; nlinarith only [hA,h.1]) |>.2

theorem endpoint_coarse_interval_bound {k d T : ℝ} (hk : 3≤k) (hd : 1<d)
    (hT : 0<T) (hT11 : T≤11) :
    d/(T+k*d)+d/(1+k*d)-(k+2)*(d/(T+k*d))*(d/(1+k*d))<
      1/(k+2)+(601/625)/((k+2)*(k+1)) := by
  have hk0 : 0<k := by linarith
  have hd0 : 0<d := by linarith
  have h1 : 0<1+k*d := by positivity
  have h2 : 0<T+k*d := by positivity
  have hkp1 : 0<k+1 := by linarith
  have hkp2 : 0<k+2 := by linarith
  have hc : 0≤(k+1)*(2*d-1)-(601/625)*(1+k*d) := by
    have he : (k+1)*(2*d-1)-(601/625)*(1+k*d)=
        (d-1)*((649/625)*k+2)+(24/625)*(k+1) := by ring
    rw [he]
    positivity
  have hn := endpoint_coarse_interval_discriminant hk d
  have hdiff := mul_nonneg (sub_nonneg.mpr hT11) hc
  have hp : 0<(601/625:ℝ)*(1+k*d)*(T+k*d)-(k+1)*(2*d-1)*(T-2*d) := by
    nlinarith only [hn,hdiff]
  have hid : (1/(k+2)+(601/625)/((k+2)*(k+1)))-
      (d/(T+k*d)+d/(1+k*d)-(k+2)*(d/(T+k*d))*(d/(1+k*d)))=
      ((601/625:ℝ)*(1+k*d)*(T+k*d)-(k+1)*(2*d-1)*(T-2*d))/
        ((k+2)*(k+1)*(1+k*d)*(T+k*d)) := by
    field_simp
    ring
  apply sub_pos.mp
  rw [hid]
  exact div_pos hp (by positivity)

theorem endpoint_coarse_rows_square_bound {m : ℕ} (hm : 5≤m) (r : Fin m → ℝ)
    (hs : ∑ i,r i=1) {d T : ℝ} (hd : 1<d) (hT : 0<T) (hT11 : T≤11)
    (hl : ∀ i,d/(T+((m:ℝ)-2)*d)≤r i)
    (hu : ∀ i,r i≤d/(1+((m:ℝ)-2)*d)) :
    (∑ i,(r i)^2)<1/(m:ℝ)+(601/625)/((m:ℝ)*((m:ℝ)-1)) := by
  let L := d/(T+((m:ℝ)-2)*d)
  let U := d/(1+((m:ℝ)-2)*d)
  have hnon : 0≤∑ i,(r i-L)*(U-r i) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sub_nonneg.mpr (hl i)) (sub_nonneg.mpr (hu i))
  have hid : (∑ i,(r i-L)*(U-r i))=L+U-(m:ℝ)*L*U-∑ i,(r i)^2 := by
    simp_rw [show ∀ i,(r i-L)*(U-r i)=L*r i+U*r i-L*U-(r i)^2 by intro i; ring]
    rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      ← Finset.mul_sum,← Finset.mul_sum,hs]
    simp only [mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  rw [hid] at hnon
  have hmR : (5:ℝ)≤m := by exact_mod_cast hm
  have hbound := endpoint_coarse_interval_bound (k:=(m:ℝ)-2) (by linarith) hd hT hT11
  have hm2 : (m:ℝ)-2+2=(m:ℝ) := by ring
  have hm1 : (m:ℝ)-2+1=(m:ℝ)-1 := by ring
  rw [hm2,hm1] at hbound
  change L+U-(m:ℝ)*L*U<_ at hbound
  linarith only [hbound,hnon]

end DittertRybin
