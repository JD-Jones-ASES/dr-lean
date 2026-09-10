import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Scalar permanent formula on the two-independent-zero face. This module
proves the two-parameter equalization on the full closed parameter rectangle.
It does not assume or assert that an arbitrary matrix has this form.
Mathematical source: Lab P0174 `TWO_ZERO_PERMANENT_GAP.md`, equations (3)--(7). -/

namespace DittertRybin

noncomputable def twoZeroReducedPermanent (m : ℕ) (a b : ℝ) : ℝ :=
  let x := (1-a-b)/(m : ℝ)
  (m.factorial : ℝ)*x^(m-2)*
    (x^2*(1-(m : ℝ)*a)*(1-(m : ℝ)*b) +
      (m : ℝ)*x*(a^2*(1-(m : ℝ)*b)+b^2*(1-(m : ℝ)*a)) +
      (m : ℝ)*((m : ℝ)-1)*a^2*b^2)

noncomputable def twoZeroX (m : ℕ) (u : ℝ) : ℝ :=
  ((m : ℝ)-2+2*u)/(m : ℝ)^2

noncomputable def twoZeroH (m : ℕ) (u : ℝ) : ℝ :=
  let x := twoZeroX m u
  let a := (1-u)/(m : ℝ)
  x^2*u^2 + 2*(m : ℝ)*x*a^2*u + (m : ℝ)*((m : ℝ)-1)*a^4

noncomputable def twoZeroCubic (m : ℕ) (u : ℝ) : ℝ :=
  ((m : ℝ)^2+3*(m : ℝ)+4)*u^3 -
    ((m : ℝ)^2+3*(m : ℝ)+8)*u^2 +
    ((m : ℝ)^2+(m : ℝ)+4)*u-(m : ℝ)

noncomputable def twoZeroUnivariate (m : ℕ) (u : ℝ) : ℝ :=
  (m.factorial : ℝ)*(twoZeroX m u)^(m-2)*twoZeroH m u

/-- The coefficient controlling equalization stays positive even at either
exceptional-diagonal-zero boundary. -/
theorem twoZero_equalization_coefficient {M s p : ℝ} (hM : 4 ≤ M)
    (hs : 0 ≤ s) (hsM : s ≤ 2/M) (hp : p ≤ s^2/4) :
    1/4 ≤ (1-s)*(1+(M+1)*s)-M*(M-1)*(p+s^2/4) := by
  have hM0 : 0 < M := by linarith
  have hM1 : 0 ≤ M*(M-1) := mul_nonneg hM0.le (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hp hM1
  have hchord : 0 ≤ (M^2+M+2)/2*s*(2/M-s) := by positivity
  have hidentity :
      (1-s)*(1+(M+1)*s)-M*(M-1)*(s^2/4+s^2/4) =
        1-(1+2/M)*s+(M^2+M+2)/2*s*(2/M-s) := by
    field_simp
    ring
  have hlinear := mul_le_mul_of_nonneg_left hsM (show 0 ≤ 1+2/M by positivity)
  have hfloor : 1/4 ≤ 1-(1+2/M)*(2/M) := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hM0)).mp
    field_simp
    nlinarith [sq_nonneg (M-4)]
  nlinarith only [hmul,hidentity,hchord,hlinear,hfloor]


/-- Exact algebraic difference between the original pair and its equalization. -/
theorem twoZeroReducedPermanent_equalization_identity {m : ℕ} (hm : 0 < m)
    (a b : ℝ) :
    twoZeroReducedPermanent m a b - twoZeroReducedPermanent m ((a+b)/2) ((a+b)/2) =
      (m.factorial : ℝ)*((1-a-b)/(m : ℝ))^(m-2)*
        ((a-b)^2/4)*
        ((1-(a+b))*(1+((m : ℝ)+1)*(a+b)) -
          (m : ℝ)*((m : ℝ)-1)*(a*b+(a+b)^2/4)) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hx : (1-(a+b)/2-(a+b)/2)/(m : ℝ) = (1-a-b)/(m : ℝ) := by ring
  unfold twoZeroReducedPermanent
  rw [hx]
  field_simp
  ring

/-- Equalizing the two exceptional parameters never raises the permanent.
The original parameters range over the entire closed feasible rectangle. -/
theorem twoZeroReducedPermanent_equalize {m : ℕ} (hm : 4 ≤ m)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ 1/(m : ℝ)) (hbM : b ≤ 1/(m : ℝ)) :
    twoZeroReducedPermanent m ((a+b)/2) ((a+b)/2) ≤ twoZeroReducedPermanent m a b := by
  have hM : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by positivity
  have hs : a+b ≤ 2/(m : ℝ) := calc
    a+b ≤ 1/(m : ℝ)+1/(m : ℝ) := add_le_add haM hbM
    _ = _ := by ring
  have hs1 : a+b ≤ 1 := by
    have hi : 2/(m : ℝ) ≤ 1 := (div_le_one hM0).mpr (by linarith)
    exact hs.trans hi
  have hc := twoZero_equalization_coefficient hM (by positivity : 0 ≤ a+b) hs
    (show a*b ≤ (a+b)^2/4 by nlinarith [sq_nonneg (a-b)])
  have hi := twoZeroReducedPermanent_equalization_identity (by omega : 0 < m) a b
  have hn : 0 ≤ (m.factorial : ℝ)*((1-a-b)/(m : ℝ))^(m-2)*((a-b)^2/4)*
      ((1-(a+b))*(1+((m : ℝ)+1)*(a+b)) -
        (m : ℝ)*((m : ℝ)-1)*(a*b+(a+b)^2/4)) := by
    have hx : 0 ≤ (1-a-b)/(m : ℝ) := div_nonneg (by linarith) hM0.le
    positivity
  linarith

/-- The equalized parameters are exactly the univariate parametrization. -/
theorem twoZeroReducedPermanent_diagonal {m : ℕ} (hm : 0 < m) (u : ℝ) :
    twoZeroReducedPermanent m ((1-u)/(m : ℝ)) ((1-u)/(m : ℝ)) =
      twoZeroUnivariate m u := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hx : (1-(1-u)/(m : ℝ)-(1-u)/(m : ℝ))/(m : ℝ) = twoZeroX m u := by
    unfold twoZeroX
    field_simp
    ring
  unfold twoZeroReducedPermanent twoZeroUnivariate twoZeroH
  rw [hx]
  field_simp
  ring


/-- Equalization is strict whenever the two exceptional parameters differ. -/
theorem twoZeroReducedPermanent_equalize_lt {m : ℕ} (hm : 4 ≤ m)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (haM : a ≤ 1/(m : ℝ)) (hbM : b ≤ 1/(m : ℝ)) (hab : a ≠ b) :
    twoZeroReducedPermanent m ((a+b)/2) ((a+b)/2) < twoZeroReducedPermanent m a b := by
  have hM : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by positivity
  have hs : a+b ≤ 2/(m : ℝ) := calc
    a+b ≤ 1/(m : ℝ)+1/(m : ℝ) := add_le_add haM hbM
    _ = _ := by ring
  have hs1 : a+b < 1 := hs.trans_lt ((div_lt_one hM0).mpr (by linarith))
  have hx : 0 < (1-a-b)/(m : ℝ) := div_pos (by linarith) hM0
  have hc := twoZero_equalization_coefficient hM (by positivity : 0 ≤ a+b) hs
    (show a*b ≤ (a+b)^2/4 by nlinarith [sq_nonneg (a-b)])
  have hcpos : 0 < (1-(a+b))*(1+((m : ℝ)+1)*(a+b)) -
      (m : ℝ)*((m : ℝ)-1)*(a*b+(a+b)^2/4) := by linarith
  have habsq : 0 < (a-b)^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hab)
  have hi := twoZeroReducedPermanent_equalization_identity (by omega : 0 < m) a b
  have hp : 0 < (m.factorial : ℝ)*((1-a-b)/(m : ℝ))^(m-2)*((a-b)^2/4)*
      ((1-(a+b))*(1+((m : ℝ)+1)*(a+b)) -
        (m : ℝ)*((m : ℝ)-1)*(a*b+(a+b)^2/4)) := by positivity
  linarith

end DittertRybin
