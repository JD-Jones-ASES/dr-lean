import DR.Square.OrderThreeBoundary
import DR.Square.OrderThreePositive

/-! The remaining finite stationary support faces at order three. -/

namespace DittertRybin

/-- The polynomial stationarity equations exclude the symmetrized one-zero face. -/
theorem orderThree_zero_rectangle_one_one {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hleft : -a*b - 4*a*c + b^2 + 2*b*c + 4*c^2 = 0)
    (hright : a^2 - a*b + 2*a*c - 4*b*c + 4*c^2 = 0)
    (hzero : a^2 - 3*a*b + b^2 + 6*c^2 ≤ 0) : False := by
  have hab : (b-a)*(a+b+6*c) = 0 := by nlinarith
  have hba : b = a := sub_eq_zero.mp ((mul_eq_zero.mp hab).resolve_right (by positivity))
  subst b
  have hac : c*(a-2*c) = 0 := by nlinarith
  have ha2 : a = 2*c := sub_eq_zero.mp ((mul_eq_zero.mp hac).resolve_left hc.ne')
  rw [ha2] at hzero
  nlinarith [sq_pos_of_pos hc]

theorem orderThree_zero_rectangle_one_two {a b c : ℝ}
    (hb : 0 < b) (hc : 0 < c)
    (hcommon : b*(a-4*b+4*c) = 0)
    (hzero : -c*(a-6*b-c) ≤ 0) : False := by
  have heq := (mul_eq_zero.mp hcommon).resolve_left hb.ne'
  have hpos := mul_pos hc (show 0 < 6*b+c-a by linarith)
  nlinarith

theorem orderThree_zero_rectangle_two_two {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hleft : -a*(a-2*b-c) = 0)
    (hright : b*(2*a-b+c) = 0) : False := by
  have h0 := (mul_eq_zero.mp hleft).resolve_left (neg_ne_zero.mpr ha.ne')
  have h1 := (mul_eq_zero.mp hright).resolve_left hb.ne'
  linarith

/-- A singleton, the opposite doubleton, and a full column after averaging
the two equal-support rows. -/
theorem orderThree_singleton_opposite_full {a b c d : ℝ}
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcommon : -2*b*(a-c-d) = 0)
    (hmisscol : -a*c-a*d+b*c+4*b*d ≤ 0)
    (hmissrow : a*b+a*d-b^2+c*d-d^2 ≤ 0) : False := by
  have ha : a = c+d := by
    have h := (mul_eq_zero.mp hcommon).resolve_left (by positivity)
    linarith
  have hab : b < a := by
    by_contra hnot
    have h := mul_nonneg (show 0 ≤ b-a from sub_nonneg.mpr (le_of_not_gt hnot))
      (show 0 ≤ c+d by positivity)
    nlinarith [mul_pos hb hd]
  have h1 := mul_pos hb (sub_pos.mpr hab)
  have h2 := mul_pos hd (show 0 < a+c-d by linarith)
  nlinarith

/-- In a six-cycle support, a pair of proper columns must agree on their
exclusive entries, shared entries, and the two remaining masses. -/
theorem orderThree_cycle_pair_equal {a b e f x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (he : 0 < e) (hf : 0 < f) (hx : 0 < x) (hy : 0 < y)
    (hcommon : -x*e+y*b+(x+y)*(a-f) = 0)
    (hleft : 0 ≤ -(x+y)*e+(x+y)*b+x*(a-f))
    (hright : -(x+y)*e+(x+y)*b+y*(a-f) ≤ 0)
    (hmiss0 : f*(b-e)+(y+b-x-e)*a ≤ 0)
    (hmiss2 : a*(e-b)+(x+e-y-b)*f ≤ 0) : x = y ∧ b = e ∧ a = f := by
  have hE : 0 < x+y+0 := by linarith
  obtain ⟨hL, hR⟩ := orderThree_proper_pair_schur (a := a) (b := b) (e := e)
    (f := f) (x := x) (y := y) (z := 0) hE (by simpa using hcommon)
      (by simpa using hleft) (by simpa using hright)
  have hD := orderThree_proper_pair_D_pos hb he hx.le hy.le (by norm_num) hE hL hR
  have hDs : 0 < y^2+y*x+x^2-(0:ℝ)^2 := by nlinarith
  have hRs : e*y*(2*(y+x+0)-y) ≤ b*(y^2+y*x+x^2-(0:ℝ)^2) := by
    convert hL using 1 <;> ring
  have hr : x+e = y+b := by
    apply le_antisymm
    · by_contra hnot
      have hgap : 0 < x+e-y-b := by linarith
      have hbe : b ≤ e := by
        by_contra hn
        have hxy : y < x := by linarith
        exact hn (orderThree_proper_pair_entry_order hb hy.le (by norm_num) hxy hD hR)
      have h1 := mul_nonneg ha.le (sub_nonneg.mpr hbe)
      have h2 := mul_pos hgap hf
      nlinarith
    · by_contra hnot
      have hgap : 0 < y+b-x-e := by linarith
      have heb : e ≤ b := by
        by_contra hn
        have hyx : x < y := by linarith
        exact hn (orderThree_proper_pair_entry_order he hx.le (by norm_num) hyx hDs hRs)
      have h1 := mul_nonneg hf.le (sub_nonneg.mpr heb)
      have h2 := mul_pos hgap ha
      nlinarith
  have hxy : x = y := by
    apply le_antisymm
    · by_contra hn
      have h := orderThree_proper_pair_entry_order hb hy.le (by norm_num)
        (show y < x by linarith) hD hR
      linarith
    · by_contra hn
      have h := orderThree_proper_pair_entry_order he hx.le (by norm_num)
        (show x < y by linarith) hDs hRs
      linarith
  have hbe : b = e := by linarith
  have haf : a = f := by
    have hid : (x+y)*(a-f) = 0 := by rw [hxy, hbe] at hcommon; nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hid).resolve_left (by positivity))
  exact ⟨hxy, hbe, haf⟩

/-- The remaining supported-cell equations on the symmetrized six-cycle
have a strictly positive elimination factor. -/
theorem orderThree_cycle_last_equal {a b x : ℝ}
    (hb : 0 < b) (hx : 0 < x)
    (hp : a*(2*b+x)-(b^2+b*x+x^2) = 0)
    (hq : a^2+a*b-a*x+b^2-2*b*x = 0) : a = b ∧ x = b := by
  have hid : b*(b-x)*(7*b^2+6*b*x+2*x^2) = 0 := by
    linear_combination (2*b+x)^2 * hq -
      (a*(2*b+x)+(b^2+b*x+x^2)+(b-x)*(2*b+x)) * hp
  have hbx : b = x := sub_eq_zero.mp ((mul_eq_zero.mp
    ((mul_eq_zero.mp hid).resolve_right (by positivity))).resolve_left hb.ne')
  subst x
  have hab : b*(a-b) = 0 := by nlinarith
  exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hab).resolve_left hb.ne'), rfl⟩

end DittertRybin
