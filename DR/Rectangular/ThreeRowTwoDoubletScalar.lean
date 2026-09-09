import DR.Rectangular.ThreeRowFullPairs

/-! A singularity-safe inverse obstruction for a doubleton versus a full column. -/
namespace DittertRybin

/-- The first two row equations and the missing-row inequality cannot hold when
p>r, all three residual masses are positive, and both positive-column offsets are below Z.
No matrix inverse or division by a determinant is used. -/
theorem threeRow_two_doublet_inverse_impossible {p q r x y Z : ℝ}
    (hp : r < p) (hq : 0 < q) (hr : 0 < r) (hZ : 0 < Z)
    (hx : x < Z) (hy : y < Z)
    (heq1 : (p+q+r)*x+(p+q)*y = (p+r)*Z)
    (heq2 : (p+q)*x+(p+q+r)*y = (q+r)*Z)
    (hzero : 0 ≤ (p+r)*x+(q+r)*y-(p+q+r)*Z) : False := by
  have hp0 : 0 < p := hr.trans hp
  have hpr : 0 < p-r := sub_pos.mpr hp
  let D := r*(2*p+2*q+r)
  let A := p^2+p*r+r^2-q^2
  let B := q^2+q*r+r^2-p^2
  let K := (p+q+r)^3+2*(p+q)*(p+r)*(q+r)-
    (p+q+r)*((p+q)^2+(p+r)^2+(q+r)^2)
  have hD : 0 < D := by dsimp [D]; positivity
  have hid1 : D*x = A*Z := by
    have h1 := congrArg (fun t : ℝ => (p+q+r)*t) heq1
    have h2 := congrArg (fun t : ℝ => (p+q)*t) heq2
    dsimp [D,A]
    nlinarith only [h1,h2]
  have hid2 : D*y = B*Z := by
    have h1 := congrArg (fun t : ℝ => (p+q)*t) heq1
    have h2 := congrArg (fun t : ℝ => (p+q+r)*t) heq2
    dsimp [D,B]
    nlinarith only [h1,h2]
  have hK : K ≤ 0 := by
    have hz := mul_nonneg (le_of_lt hD) hzero
    have h1 := congrArg (fun t : ℝ => (p+r)*t) hid1
    have h2 := congrArg (fun t : ℝ => (q+r)*t) hid2
    have hprod : 0 ≤ -K*Z := by dsimp [D,A,B,K] at *; nlinarith only [hz,h1,h2]
    have hn := nonneg_of_mul_nonneg_left hprod hZ
    linarith only [hn]
  have hA : A < D := by
    have h := mul_lt_mul_of_pos_left hx hD
    rw [hid1] at h
    exact (mul_lt_mul_iff_left₀ hZ).mp h
  have hB : B < D := by
    have h := mul_lt_mul_of_pos_left hy hD
    rw [hid2] at h
    exact (mul_lt_mul_iff_left₀ hZ).mp h
  rcases le_total q p with hqp | hpq
  · have hH : p^2-q^2-p*r-2*q*r < 0 := by dsimp [A,D] at hA; nlinarith only [hA]
    have h1 := mul_nonneg (sub_nonneg.mpr hqp) (le_of_lt (neg_pos.mpr hH))
    have h2 : 0 < r*(3*p*q+3*q^2+q*r+r*(p-r)) := by positivity
    have hid : K = (q-p)*(p^2-q^2-p*r-2*q*r)+r*(3*p*q+3*q^2+q*r+r*(p-r)) := by dsimp [K]; ring
    nlinarith only [hK,h1,h2,hid]
  · have hqr : r < q := hp.trans_le hpq
    have hqr' : 0 < q-r := sub_pos.mpr hqr
    have hH : q^2-p^2-q*r-2*p*r < 0 := by dsimp [B,D] at hB; nlinarith only [hB]
    have h1 := mul_nonneg (sub_nonneg.mpr hpq) (le_of_lt (neg_pos.mpr hH))
    have h2 : 0 < r*(3*q*p+3*p^2+p*r+r*(q-r)) := by positivity
    have hid : K = (p-q)*(q^2-p^2-q*r-2*p*r)+r*(3*q*p+3*p^2+p*r+r*(q-r)) := by dsimp [K]; ring
    nlinarith only [hK,h1,h2,hid]

end DittertRybin
