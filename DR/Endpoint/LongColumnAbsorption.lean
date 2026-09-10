import DR.Endpoint.LongColumnVariance

/-! Scalar absorption of the retained-uniform contender comparison.
The original column maximum and the nonnegative gauge gap remain explicit
until the actual probability comparison supplies them. -/
namespace DittertRybin

theorem longColumn_absorb_variance {N a b c ρ V W g : ℝ}
    (hN : 0<N) (hb : 0≤b) (hc : 0≤c) (hW : 0≤W)
    (hsmall : b*c<1/6) (hV : V≤3*W+3*ρ^2/N)
    (hcomp : g+N*W≤N*b*c*V+a*b/(2*N)) :
    g+(N/2)*W≤a*b/(2*N)+3*b*ρ^2*c := by
  have hv := mul_le_mul_of_nonneg_left hV (mul_nonneg (mul_nonneg hN.le hb) hc)
  have hsc := mul_le_mul_of_nonneg_right hsmall.le (mul_nonneg hN.le hW)
  have hid : N*b*c*(3*W+3*ρ^2/N)=3*N*b*c*W+3*b*ρ^2*c := by
    field_simp
  rw [hid] at hv
  nlinarith only [hv,hsc,hcomp]

theorem longColumn_cap_twenty_five {N a b c ρ W g : ℝ}
    (hN : 0<N) (hc : 0≤c) (hg : 0≤g)
    (hab : a*b<1) (hbr : b*ρ^2<1)
    (habs : g+(N/2)*W≤a*b/(2*N)+3*b*ρ^2*c)
    (hsq : c^2≤4/N^2+4*W) : c<25/N := by
  have hmul := mul_le_mul_of_nonneg_right habs (by positivity : 0≤2*N)
  have hid : (a*b/(2*N)+3*b*ρ^2*c)*(2*N)=a*b+6*b*ρ^2*(N*c) := by
    field_simp
    ring
  rw [hid] at hmul
  have hw : N^2*W≤a*b+6*b*ρ^2*(N*c) := by
    nlinarith only [hmul,mul_nonneg hg hN.le]
  have hsqN := mul_le_mul_of_nonneg_right hsq (sq_nonneg N)
  have hid2 : (4/N^2+4*W)*N^2=4+4*N^2*W := by field_simp
  rw [hid2] at hsqN
  have hy : 0≤N*c := mul_nonneg hN.le hc
  have hbrN := mul_le_mul_of_nonneg_right hbr.le hy
  have hquad : (N*c)^2<8+24*(N*c) := by nlinarith only [hw,hsqN,hab,hbrN]
  apply (lt_div_iff₀ hN).mpr
  by_contra h
  have hy25 : 25≤N*c := by nlinarith only [not_lt.mp h]
  nlinarith only [hquad,mul_nonneg (show 0≤N*c-25 by linarith) (show 0≤N*c+1 by linarith)]

theorem longColumn_gap_after_cap {N a b c ρ W g : ℝ}
    (hN : 0<N) (_ha : 0≤a) (hb : 0≤b) (hρ : 0≤ρ)
    (hr : ρ≤5*a) (hW : 0≤W) (hcap : c<25/N)
    (habs : g+(N/2)*W≤a*b/(2*N)+3*b*ρ^2*c) :
    g≤a*(b/2+1875*a*b)/N := by
  have hρsq := pow_le_pow_left₀ hρ hr 2
  have hc := mul_le_mul_of_nonneg_left hcap.le
    (mul_nonneg (by positivity : (0:ℝ)≤3*b) (sq_nonneg ρ))
  have hrN := mul_le_mul_of_nonneg_left hρsq (show 0≤75*b/N by positivity)
  have hgid : a*b/(2*N)+3*b*ρ^2*(25/N)=a*b/(2*N)+(75*b/N)*ρ^2 := by ring
  have hid : a*b/(2*N)+(75*b/N)*(5*a)^2=a*(b/2+1875*a*b)/N := by ring
  rw [← hid]
  nlinarith only [habs,hc,hrN,hgid,mul_nonneg (div_nonneg hN.le (by norm_num : (0:ℝ)≤2)) hW]

end DittertRybin
