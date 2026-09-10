import DR.Endpoint.TwoZeroPolynomial
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Exact polynomial derivatives and their signs for the two-zero scalar
permanent. All identities are real polynomial identities; no numerical
root or stationary-matrix hypothesis is used. -/
namespace DittertRybin

noncomputable def twoZeroG (m : ℕ) (u : ℝ) : ℝ :=
  ((m : ℝ)^2+3*(m : ℝ)+4)*u^4 -
    2*((m : ℝ)^2+2*(m : ℝ)+4)*u^3 +
    (3*(m : ℝ)^2+2*(m : ℝ)+4)*u^2-2*(m : ℝ)^2*u+(m : ℝ)^2-(m : ℝ)

noncomputable def twoZeroGDeriv (m : ℕ) (u : ℝ) : ℝ :=
  4*((m : ℝ)^2+3*(m : ℝ)+4)*u^3 -
    6*((m : ℝ)^2+2*(m : ℝ)+4)*u^2 +
    2*(3*(m : ℝ)^2+2*(m : ℝ)+4)*u-2*(m : ℝ)^2

noncomputable def twoZeroGSecond (m : ℕ) (u : ℝ) : ℝ :=
  12*((m : ℝ)^2+3*(m : ℝ)+4)*u^2 -
    12*((m : ℝ)^2+2*(m : ℝ)+4)*u +
    2*(3*(m : ℝ)^2+2*(m : ℝ)+4)

noncomputable def twoZeroCubicDeriv (m : ℕ) (u : ℝ) : ℝ :=
  3*((m : ℝ)^2+3*(m : ℝ)+4)*u^2 -
    2*((m : ℝ)^2+3*(m : ℝ)+8)*u + ((m : ℝ)^2+(m : ℝ)+4)

theorem twoZeroH_eq_G {m : ℕ} (hm : 0 < m) (u : ℝ) :
    twoZeroH m u = twoZeroG m u/(m : ℝ)^4 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold twoZeroH twoZeroX twoZeroG
  field_simp
  ring

theorem hasDerivAt_twoZeroG (m : ℕ) (u : ℝ) :
    HasDerivAt (twoZeroG m) (twoZeroGDeriv m u) u := by
  convert (((((((hasDerivAt_id u).pow 4).const_mul ((m : ℝ)^2+3*(m : ℝ)+4)).sub
    (((hasDerivAt_id u).pow 3).const_mul (2*((m : ℝ)^2+2*(m : ℝ)+4)))).add
    (((hasDerivAt_id u).pow 2).const_mul (3*(m : ℝ)^2+2*(m : ℝ)+4))).sub
    ((hasDerivAt_id u).const_mul (2*(m : ℝ)^2))).add_const ((m : ℝ)^2)).sub_const (m : ℝ) using 1 <;> try rfl
  all_goals try dsimp [twoZeroG,twoZeroGDeriv]
  all_goals ring

theorem hasDerivAt_twoZeroGDeriv (m : ℕ) (u : ℝ) :
    HasDerivAt (twoZeroGDeriv m) (twoZeroGSecond m u) u := by
  convert (((((hasDerivAt_id u).pow 3).const_mul (4*((m : ℝ)^2+3*(m : ℝ)+4))).sub
    (((hasDerivAt_id u).pow 2).const_mul (6*((m : ℝ)^2+2*(m : ℝ)+4)))).add
    ((hasDerivAt_id u).const_mul (2*(3*(m : ℝ)^2+2*(m : ℝ)+4)))).sub_const
    (2*(m : ℝ)^2) using 1 <;> try rfl
  all_goals try dsimp [twoZeroGDeriv,twoZeroGSecond]
  all_goals ring

theorem hasDerivAt_twoZeroCubic (m : ℕ) (u : ℝ) :
    HasDerivAt (twoZeroCubic m) (twoZeroCubicDeriv m u) u := by
  convert (((((hasDerivAt_id u).pow 3).const_mul ((m : ℝ)^2+3*(m : ℝ)+4)).sub
    (((hasDerivAt_id u).pow 2).const_mul ((m : ℝ)^2+3*(m : ℝ)+8))).add
    ((hasDerivAt_id u).const_mul ((m : ℝ)^2+(m : ℝ)+4))).sub_const
    (m : ℝ) using 1 <;> try rfl
  all_goals try dsimp [twoZeroCubic,twoZeroCubicDeriv]
  all_goals ring

/-- The source cubic has strictly positive derivative on the entire real line. -/
theorem twoZeroCubicDeriv_pos {m : ℕ} (hm : 4 ≤ m) (u : ℝ) :
    0 < twoZeroCubicDeriv m u := by
  have hM : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by positivity
  have hdisc : 0 < 2*((m : ℝ)-1)*((m : ℝ)+2)*((m : ℝ)^2+2*(m : ℝ)+4) := by
    have h1 : 0 < (m : ℝ)-1 := by linarith
    positivity
  have hsq := sq_nonneg (3*((m : ℝ)^2+3*(m : ℝ)+4)*u-((m : ℝ)^2+3*(m : ℝ)+8))
  have hi : 3*((m : ℝ)^2+3*(m : ℝ)+4)*twoZeroCubicDeriv m u =
      (3*((m : ℝ)^2+3*(m : ℝ)+4)*u-((m : ℝ)^2+3*(m : ℝ)+8))^2+
        2*((m : ℝ)-1)*((m : ℝ)+2)*((m : ℝ)^2+2*(m : ℝ)+4) := by
    unfold twoZeroCubicDeriv
    ring
  have hleft : 0 < 3*((m : ℝ)^2+3*(m : ℝ)+4) := by positivity
  exact (mul_pos_iff_of_pos_left hleft).mp (by linarith only [hi,hsq,hdisc])

theorem twoZeroCubic_strictMono {m : ℕ} (hm : 4 ≤ m) : StrictMono (twoZeroCubic m) :=
  strictMono_of_deriv_pos fun u => by
    rw [(hasDerivAt_twoZeroCubic m u).deriv]
    exact twoZeroCubicDeriv_pos hm u

/-- The quartic numerator is strictly convex, without restricting u. -/
theorem twoZeroGSecond_pos {m : ℕ} (hm : 4 ≤ m) (u : ℝ) :
    0 < twoZeroGSecond m u := by
  have hM : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by positivity
  have hc : 0 < 3*(m : ℝ)^3+4*(m : ℝ)^2-8 := by
    have hcube : 0 ≤ (m : ℝ)^3 := by positivity
    nlinarith [sq_nonneg ((m : ℝ)-4)]
  have hdisc : 0 < 3*((m : ℝ)+2)*(3*(m : ℝ)^3+4*(m : ℝ)^2-8) := by positivity
  have hi : 3*((m : ℝ)^2+3*(m : ℝ)+4)*twoZeroGSecond m u =
      (6*((m : ℝ)^2+3*(m : ℝ)+4)*u-3*((m : ℝ)^2+2*(m : ℝ)+4))^2+
        3*((m : ℝ)+2)*(3*(m : ℝ)^3+4*(m : ℝ)^2-8) := by
    unfold twoZeroGSecond
    ring
  have hsq := sq_nonneg (6*((m : ℝ)^2+3*(m : ℝ)+4)*u-3*((m : ℝ)^2+2*(m : ℝ)+4))
  have hleft : 0 < 3*((m : ℝ)^2+3*(m : ℝ)+4) := by positivity
  exact (mul_pos_iff_of_pos_left hleft).mp (by linarith only [hi,hsq,hdisc])

theorem twoZeroGDeriv_strictMono {m : ℕ} (hm : 4 ≤ m) : StrictMono (twoZeroGDeriv m) :=
  strictMono_of_deriv_pos fun u => by
    rw [(hasDerivAt_twoZeroGDeriv m u).deriv]
    exact twoZeroGSecond_pos hm u


theorem twoZeroGDeriv_at_reciprocal {m : ℕ} (hm : 0 < m) :
    twoZeroGDeriv m (1/(m : ℝ)) =
      -2*((m : ℝ)^5-3*(m : ℝ)^4+(m : ℝ)^3+6*(m : ℝ)-8)/(m : ℝ)^3 := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold twoZeroGDeriv
  field_simp
  ring

theorem twoZeroGDeriv_reciprocal_neg {m : ℕ} (hm : 4 ≤ m) :
    twoZeroGDeriv m (1/(m : ℝ)) < 0 := by
  have hM : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < m := by positivity
  have hp : 0 < (m : ℝ)^4*((m : ℝ)-3)+(m : ℝ)^3+(6*(m : ℝ)-8) := by
    have h1 : 0 < (m : ℝ)-3 := by linarith
    have h2 : 0 < 6*(m : ℝ)-8 := by linarith
    positivity
  rw [twoZeroGDeriv_at_reciprocal (by omega : 0 < m)]
  apply div_neg_of_neg_of_pos _ (by positivity)
  nlinarith only [hp]

theorem hasDerivAt_twoZeroH {m : ℕ} (hm : 0 < m) (u : ℝ) :
    HasDerivAt (twoZeroH m) (twoZeroGDeriv m u/(m : ℝ)^4) u := by
  have heq : twoZeroH m = fun v => twoZeroG m v/(m : ℝ)^4 :=
    funext (twoZeroH_eq_G hm)
  rw [heq]
  exact (hasDerivAt_twoZeroG m u).div_const _

/-- The quartic factor decreases on the entire root-bracketing interval. -/
theorem twoZeroH_antitoneOn {m : ℕ} (hm : 4 ≤ m) :
    AntitoneOn (twoZeroH m) (Set.Icc 0 (1/(m : ℝ))) := by
  have hd : Differentiable ℝ (twoZeroH m) := fun u =>
    (hasDerivAt_twoZeroH (m := m) (by omega) u).differentiableAt
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact hd.continuous.continuousOn
  · exact hd.differentiableOn
  · intro u hu
    have hum : u ≤ 1/(m : ℝ) := (interior_subset hu).2
    rw [(hasDerivAt_twoZeroH (by omega) u).deriv]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact ((twoZeroGDeriv_strictMono hm).monotone hum).trans
      (twoZeroGDeriv_reciprocal_neg hm).le

theorem twoZeroX_pos {m : ℕ} (hm : 4 ≤ m) {u : ℝ} (hu : 0 ≤ u) :
    0 < twoZeroX m u := by
  have hM : (4 : ℝ) ≤ m := by exact_mod_cast hm
  unfold twoZeroX
  exact div_pos (by linarith) (by positivity)

theorem twoZeroX_monotone (m : ℕ) : Monotone (twoZeroX m) := by
  intro u v huv
  unfold twoZeroX
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem twoZeroH_nonneg {m : ℕ} (hm : 4 ≤ m) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ twoZeroH m u := by
  have hx := twoZeroX_pos hm hu
  have hM : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have h1 : 0 ≤ (m : ℝ)-1 := by linarith
  unfold twoZeroH
  positivity

theorem hasDerivAt_twoZeroX (m : ℕ) (u : ℝ) :
    HasDerivAt (twoZeroX m) (2/(m : ℝ)^2) u := by
  convert (((hasDerivAt_id u).const_mul 2).const_add ((m : ℝ)-2)).div_const
    ((m : ℝ)^2) using 1 <;> try rfl
  all_goals ring

/-- Exact factorization of the derivative: the sole varying sign is the cubic. -/
theorem hasDerivAt_twoZeroUnivariate {m : ℕ} (hm : 4 ≤ m) (u : ℝ) :
    HasDerivAt (twoZeroUnivariate m)
      (2*(m.factorial : ℝ)*(twoZeroX m u)^(m-3)/(m : ℝ)^6*
        ((m : ℝ)-2+((m : ℝ)+2)*u)*twoZeroCubic m u) u := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hexp : m-2-1 = m-3 := by omega
  have hpow : (twoZeroX m u)^(m-2) = (twoZeroX m u)^(m-3)*twoZeroX m u := by
    have he : m-2 = (m-3)+1 := by omega
    rw [he,pow_succ]
  have hd := (((hasDerivAt_twoZeroX m u).pow (m-2)).mul
    ((hasDerivAt_twoZeroG m u).div_const ((m : ℝ)^4))).const_mul (m.factorial : ℝ)
  convert hd using 1 <;> try rfl
  · funext v
    simp only [twoZeroUnivariate,twoZeroH_eq_G (by omega : 0 < m),Pi.mul_apply,Pi.pow_apply]
    ring
  · change _ = (m.factorial : ℝ)*_
    dsimp only [Pi.pow_apply]
    rw [hexp,hpow,Nat.cast_sub (by omega : 2 ≤ m)]
    norm_num only [Nat.cast_ofNat]
    unfold twoZeroX twoZeroG twoZeroGDeriv twoZeroCubic
    field_simp
    ring

end DittertRybin
