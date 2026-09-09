import DR.ElementarySymmetricBoundsRoots

/-! Newton's normalized coefficient inequality from real splitting and Rolle. -/

namespace DittertRybin
open Polynomial

noncomputable def normalizedPolynomialCoefficient (p : ℝ[X]) (k : ℕ) : ℝ :=
  p.coeff k / (p.natDegree.choose k : ℝ)

theorem natDegree_iterate_derivative_real (p : ℝ[X]) (k : ℕ) :
    (Polynomial.derivative^[k] p).natDegree = p.natDegree-k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply',Polynomial.natDegree_derivative,ih]
      omega

theorem eval_iterate_derivative_zero_normalized (p : ℝ[X]) {k : ℕ}
    (hk : k ≤ p.natDegree) :
    (Polynomial.derivative^[k] p).eval 0 =
      (p.natDegree.descFactorial k:ℝ)*normalizedPolynomialCoefficient p k := by
  rw [← Polynomial.coeff_zero_eq_eval_zero,Polynomial.coeff_iterate_derivative]
  simp only [zero_add,Nat.descFactorial_self,nsmul_eq_mul]
  unfold normalizedPolynomialCoefficient
  rw [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  have hc : (p.natDegree.choose k:ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hk).ne'
  field_simp

/-- Normalized Newton inequalities, without sign or simple-root assumptions. -/
theorem normalizedCoefficient_newton {p : ℝ[X]} (hp : p.Splits)
    {j : ℕ} (hj : j+2 ≤ p.natDegree) :
    normalizedPolynomialCoefficient p j * normalizedPolynomialCoefficient p (j+2) ≤
      normalizedPolynomialCoefficient p (j+1)^2 := by
  let q := Polynomial.derivative^[j] p
  let d := p.natDegree-j
  let a : ℝ := p.natDegree.descFactorial j
  have hq : q.Splits := real_splits_iterate_derivative hp j
  have hqd : q.natDegree = d := natDegree_iterate_derivative_real p j
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hdR : (2:ℝ) ≤ d := by exact_mod_cast hd
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast (Nat.descFactorial_pos.mpr (show j ≤ p.natDegree by omega))
  have he0 : q.eval 0 = a*normalizedPolynomialCoefficient p j :=
    eval_iterate_derivative_zero_normalized p (by omega)
  have he1 : q.derivative.eval 0 =
      (p.natDegree.descFactorial (j+1):ℝ)*normalizedPolynomialCoefficient p (j+1) := by
    simpa only [q,Function.iterate_succ_apply'] using
      eval_iterate_derivative_zero_normalized p (show j+1 ≤ p.natDegree by omega)
  have he2 : q.derivative.derivative.eval 0 =
      (p.natDegree.descFactorial (j+2):ℝ)*normalizedPolynomialCoefficient p (j+2) := by
    simpa only [q,Function.iterate_succ_apply'] using
      eval_iterate_derivative_zero_normalized p hj
  have hcast : ((p.natDegree-(j+1):ℕ):ℝ) = (d:ℝ)-1 := by
    have hh : p.natDegree-(j+1) = d-1 := by dsimp [d]; omega
    rw [hh,Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  rw [Nat.descFactorial_succ,Nat.cast_mul] at he1
  rw [show j+2 = (j+1)+1 by omega,Nat.descFactorial_succ,
    Nat.descFactorial_succ,Nat.cast_mul,Nat.cast_mul,hcast] at he2
  change q.derivative.eval 0 = (d:ℝ)*a*normalizedPolynomialCoefficient p (j+1) at he1
  change q.derivative.derivative.eval 0 =
    ((d:ℝ)-1)*((d:ℝ)*a)*normalizedPolynomialCoefficient p (j+2) at he2
  have h := real_splits_laguerre hq (by rw [hqd]; omega) 0
  rw [hqd,he0,he1,he2] at h
  have hd0 : (0:ℝ) < d := by linarith
  have hd1 : 0 < (d:ℝ)-1 := by linarith
  have hfactor : 0 < (d:ℝ)^2*((d:ℝ)-1)*a^2 := by positivity
  apply (mul_le_mul_iff_of_pos_left hfactor).mp
  convert h using 1 <;> first | rfl | ring

end DittertRybin
