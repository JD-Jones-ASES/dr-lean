import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Scalar first-order exclusion for S columns `(0,b,b)` and T columns `(c,d,d)`.
The inequalities specialize the zero-rectangle stationarity equations to three rows.
All four first-order conditions include the inequalities at actual zero entries. -/

namespace DittertRybin

/-- The column conditions force a strict residual-mass ratio and c > b.
The product bound is the boundary-safe form of X/Y ≤ c/d. -/
theorem threeRow_single_doublet_column_forces {b c d X Y : ℝ}
    (hc : 0 < c) (hd : 0 < d) (hX : 0 ≤ X) (hY : 0 < Y)
    (hbound : d * X ≤ c * Y)
    (heq : (b-d)*(X+4*Y) = c*(X+Y))
    (hzero : 0 ≤ -(X+2*Y)*c + 2*(X+Y)*(b-d)) :
    2*Y < X ∧ b < c := by
  have hden : 0 < X+4*Y := by positivity
  have hprod := mul_nonneg hzero (le_of_lt hden)
  have hid := congrArg (fun z : ℝ => 2*(X+Y)*z) heq
  have hquad : 0 ≤ X^2-2*X*Y-6*Y^2 := by
    have hq : 0 ≤ c*(X^2-2*X*Y-6*Y^2) := by nlinarith only [hprod, hid]
    exact nonneg_of_mul_nonneg_right hq hc
  have hratio : 2*Y < X := by
    by_contra h
    have hs := mul_nonneg hX (sub_nonneg.mpr (le_of_not_gt h))
    nlinarith [sq_pos_of_pos hY]
  refine ⟨hratio, ?_⟩
  by_contra h
  have hcb : c ≤ b := le_of_not_gt h
  have hm := mul_nonneg (sub_nonneg.mpr hcb) (le_of_lt hden)
  have hdxy := mul_pos hd (sub_pos.mpr hratio)
  nlinarith only [heq, hm, hbound, hdxy]

/-- An elementary quadratic classification, with integer counts represented as reals.
The assumptions S,T≥1 and S+T≥3 retain the smallest physical multiplicities. -/
theorem threeRow_single_doublet_quadratic_alternatives {S T b d : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (hN : 3 ≤ S+T)
    (hb : 0 < b) (hd : 0 < d)
    (hq : 0 ≤ S*T*(b+d)^2 - ((3*S-2)*b+T*d)*(S*b+(3*T-2)*d)) :
    3*T-2 ≤ S ∨ (3*S-2 < T ∧ 2*d < b) := by
  by_cases hZ : 3*T-2 ≤ S
  · exact Or.inl hZ
  have hconst : S-3*T+2 < 0 := by linarith
  have hlin : -8*S*T+6*S+6*T-4 ≤ 0 := by
    have h1 := mul_nonneg (by linarith : 0 ≤ S-1) (by linarith : 0 ≤ 4*T-3)
    nlinarith only [h1, hT]
  have hcst := mul_neg_of_pos_of_neg (mul_pos (by linarith : 0 < T) (sq_pos_of_pos hd)) hconst
  have hq' : 0 ≤ S*(T-3*S+2)*b^2 + (-8*S*T+6*S+6*T-4)*b*d + T*(S-3*T+2)*d^2 := by
    nlinarith only [hq]
  have hlead : 3*S-2 < T := by
    by_contra h
    have ha := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith : 0 ≤ S) (sq_nonneg b)) (by linarith : T-3*S+2 ≤ 0)
    have hl := mul_nonpos_of_nonpos_of_nonneg hlin (le_of_lt (mul_pos hb hd))
    nlinarith only [hq', ha, hl, hcst]
  refine Or.inr ⟨hlead, ?_⟩
  by_contra h
  have ha := mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (mul_pos (mul_pos (by linarith : 0 < S) (by linarith : 0 < T-3*S+2)) hb))
    (by linarith : b-2*d ≤ 0)
  have hm := mul_nonneg (mul_nonneg (by linarith : 0 ≤ S-1) (by linarith : 0 ≤ 3*S+3*T-2))
    (le_of_lt (mul_pos hb hd))
  nlinarith only [hq', ha, hm, hcst]

/-- The mixed size alternative contradicts the positive-row derivative identity. -/
theorem threeRow_single_doublet_mixed_impossible {S T b c d : ℝ}
    (_hS : 1 ≤ S) (hT : 2 ≤ T) (hb : 0 < b) (hd : 0 < d) (hcd : d < c)
    (hZ : 3*T-2 ≤ S)
    (hratio : 2*((S-1)*b+(T-1)*d) < (T-1)*c)
    (heq : (c-d)*(S*b+(3*T-2)*d) = S*b*(b+d)) : False := by
  let K := 3*T-2
  have hK : 0 < K := by dsimp [K]; linarith
  have hSK : K ≤ S := hZ
  have ht : 0 < T-1 := by linarith
  have he : (c-d)*(S*b+K*d) = S*b*(b+d) := heq
  have hm := mul_nonneg (le_of_lt (sub_pos.mpr hcd))
    (mul_nonneg (le_of_lt hb) (sub_nonneg.mpr hSK))
  have ha : K*(c-d) ≤ S*b := by
    have hprod : 0 ≤ (b+d)*(S*b-K*(c-d)) := by nlinarith only [he, hm]
    have hinner := nonneg_of_mul_nonneg_right hprod (add_pos hb hd)
    linarith only [hinner]
  have hcount1 := mul_nonneg (sub_nonneg.mpr hSK) (by linarith : 0 ≤ 5*T-3)
  have hcount2 := mul_nonneg (by positivity : 0 ≤ 5*K) (le_of_lt ht)
  have hcount : S*(T-1) ≤ 2*K*(S-1) := by dsimp [K] at *; nlinarith only [hcount1, hcount2]
  have hlow : 2*(S-1)*b < (T-1)*(c-d) := by nlinarith only [hratio, mul_pos ht hd]
  have hupper := mul_le_mul_of_nonneg_left ha (le_of_lt ht)
  have hlower := mul_lt_mul_of_pos_left hlow hK
  have hscaled := mul_le_mul_of_nonneg_right hcount (le_of_lt hb)
  nlinarith only [hupper, hlower, hscaled]

/-- The two strict size alternatives contradict the positive-row identity. -/
theorem threeRow_single_doublet_strict_impossible {S T b c d : ℝ}
    (hS : 1 ≤ S) (hb : 0 < b) (hd : 0 < d) (hcb : b < c)
    (hT : 3*S-1 ≤ T) (hbd : 2*d < b)
    (heq : (c-d)*(S*b+(3*T-2)*d) = S*b*(b+d)) : False := by
  let K := 3*T-2
  have hK4 : 4*S ≤ K := by dsimp [K]; linarith
  have hK : 0 < K := by linarith
  have hden : 0 < S*b+K*d := by positivity
  have hstrict := mul_pos (sub_pos.mpr hcb) hden
  have he : (c-d)*(S*b+K*d) = S*b*(b+d) := heq
  have hnegative : d*(K*(b-d)-2*S*b) < 0 := by nlinarith only [he, hstrict]
  have hp1 := mul_nonneg (by linarith : 0 ≤ K-2*S) (le_of_lt (sub_pos.mpr hbd))
  have hp2 := mul_nonneg (by linarith : 0 ≤ K-4*S) (le_of_lt hd)
  have hp : 0 ≤ K*(b-d)-2*S*b := by nlinarith only [hp1, hp2]
  exact (not_lt_of_ge (mul_nonneg (le_of_lt hd) hp)) hnegative

/-- No positive three-block representative with a nonempty zero block satisfies
all full-simplex first-order conditions when there are at least three columns. -/
theorem threeRow_single_doublet_full_kkt_impossible {S T : ℕ} {b c d : ℝ}
    (hS : 1 ≤ S) (hT : 1 ≤ T) (hN : 3 ≤ S+T)
    (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hcol : (b-d)*(((T:ℝ)-1)*c+4*(((S:ℝ)-1)*b+((T:ℝ)-1)*d)) =
      c*(((T:ℝ)-1)*c+((S:ℝ)-1)*b+((T:ℝ)-1)*d))
    (hcolzero : 0 ≤ -(((T:ℝ)-1)*c+2*(((S:ℝ)-1)*b+((T:ℝ)-1)*d))*c +
      2*(((T:ℝ)-1)*c+((S:ℝ)-1)*b+((T:ℝ)-1)*d)*(b-d))
    (hrow : (c-d)*((S:ℝ)*b+(3*(T:ℝ)-2)*d) = (S:ℝ)*b*(b+d))
    (hrowzero : b*((3*(S:ℝ)-2)*b+(T:ℝ)*d) ≤ (T:ℝ)*(c-d)*(b+d)) : False := by
  have hSr : (1:ℝ) ≤ S := by exact_mod_cast hS
  have hTr : (1:ℝ) ≤ T := by exact_mod_cast hT
  have hNr : (3:ℝ) ≤ (S:ℝ)+T := by exact_mod_cast hN
  let X := ((T:ℝ)-1)*c
  let Y := ((S:ℝ)-1)*b+((T:ℝ)-1)*d
  have hX : 0 ≤ X := mul_nonneg (by linarith) (le_of_lt hc)
  have hY : 0 < Y := by
    have hS0 : 0 ≤ (S:ℝ)-1 := by linarith
    have hT0 : 0 ≤ (T:ℝ)-1 := by linarith
    have hm1 := mul_nonneg hS0 (le_of_lt hb)
    have hm2 := mul_nonneg hT0 (le_of_lt hd)
    by_cases hs : 1 < (S:ℝ)
    · have hp := mul_pos (sub_pos.mpr hs) hb
      dsimp [Y]; linarith
    · have ht : 1 < (T:ℝ) := by linarith
      have hp := mul_pos (sub_pos.mpr ht) hd
      dsimp [Y]; linarith
  have hbound : d*X ≤ c*Y := by
    have hp := mul_nonneg (le_of_lt hc) (mul_nonneg (by linarith : 0 ≤ (S:ℝ)-1) (le_of_lt hb))
    dsimp [X,Y]; nlinarith only [hp]
  obtain ⟨hratio, hcb⟩ := threeRow_single_doublet_column_forces hc hd hX hY hbound
    (by dsimp [X,Y]; nlinarith only [hcol]) (by dsimp [X,Y]; nlinarith only [hcolzero])
  have ht2 : 2 ≤ T := by
    by_contra h
    have ht1 : T = 1 := by omega
    simp [X, ht1] at hratio
    linarith
  have ht2r : (2:ℝ) ≤ T := by exact_mod_cast ht2
  have hcd : d < c := by
    have hp := mul_nonneg (by linarith : 0 ≤ (S:ℝ)-1) (le_of_lt hb)
    have ht : 0 < (T:ℝ)-1 := by linarith
    have hprod : 0 < ((T:ℝ)-1)*(c-d) := by dsimp [X,Y] at hratio; nlinarith [mul_pos ht hd]
    exact sub_pos.mp (pos_of_mul_pos_right hprod (le_of_lt ht))
  have hK : 0 < 3*(T:ℝ)-2 := by linarith
  have hSpos : (0:ℝ) < S := by linarith
  have hden : 0 < (S:ℝ)*b+(3*(T:ℝ)-2)*d := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hrowzero (le_of_lt hden)
  have hid := congrArg (fun z : ℝ => (T:ℝ)*(b+d)*z) hrow
  have hquad : 0 ≤ (S:ℝ)*(T:ℝ)*(b+d)^2 - ((3*(S:ℝ)-2)*b+(T:ℝ)*d)*((S:ℝ)*b+(3*(T:ℝ)-2)*d) := by
    have hprod : 0 ≤ b*((S:ℝ)*(T:ℝ)*(b+d)^2 - ((3*(S:ℝ)-2)*b+(T:ℝ)*d)*((S:ℝ)*b+(3*(T:ℝ)-2)*d)) := by
      nlinarith only [hscaled, hid]
    exact nonneg_of_mul_nonneg_right hprod hb
  rcases threeRow_single_doublet_quadratic_alternatives hSr hTr hNr hb hd hquad with hz | ⟨hf, hbd⟩
  · exact threeRow_single_doublet_mixed_impossible hSr ht2r hb hd hcd hz hratio hrow
  · have hnat : 3*S < T+2 := by exact_mod_cast (show 3*(S:ℝ) < (T:ℝ)+2 by linarith)
    have hreal : 3*(S:ℝ) ≤ (T:ℝ)+1 := by exact_mod_cast (show 3*S ≤ T+1 by omega)
    exact threeRow_single_doublet_strict_impossible hSr hb hd hcb (by linarith) hbd hrow

end DittertRybin
