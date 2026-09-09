import DR.Certificates.FourRowMinorantData
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin

/-! Exact tensor degree elevation of the 21-term compactified repeated-row objective. -/

namespace DittertRybin.Certificates.FourRowMinorant
open scoped BigOperators

noncomputable def degree34Moment (a : Fin 3) (i : Fin 35) : ℝ :=
  (degree34MomentNumerator a i:ℝ)/1122

theorem degree34Moment_eq_choose (a : Fin 3) (i : Fin 35) :
    degree34Moment a i = algebraMap ℚ ℝ
      (((i:ℕ).choose a:ℚ)/((34:ℕ).choose a:ℚ)) := by
  fin_cases a
  · norm_num [degree34Moment,degree34MomentNumerator]
  · norm_num [degree34Moment,degree34MomentNumerator]
    ring
  · norm_num [degree34Moment,degree34MomentNumerator,Nat.cast_choose_two]
    ring

theorem degree34Moment_expansion (a : Fin 3) (x : ℝ) :
    x^(a:ℕ) = ∑ i : Fin 35, degree34Moment a i*bernsteinWeight 34 i x := by
  simp_rw [degree34Moment_eq_choose]
  simpa only [Finset.sum_range,bernsteinWeight] using
    power_bernstein_expansion x 34 a (by omega)

noncomputable def compactPowerValue (X T Z : ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    (compactPowerCoefficient a b c:ℝ)*X^(a:ℕ)*T^(b:ℕ)*Z^(c:ℕ)

noncomputable def compactBernsteinCoefficient (i j k : Fin 35) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    (compactPowerCoefficient a b c:ℝ)*degree34Moment a i*degree34Moment b j*degree34Moment c k

theorem compactBernsteinCoefficient_eq_numerator (i j k : Fin 35) :
    compactBernsteinCoefficient i j k = (compactBernsteinNumerator i j k:ℝ)/1122^3 := by
  norm_num [compactBernsteinCoefficient,compactPowerCoefficient,Fin.sum_univ_succ,
    compactBernsteinNumerator,degree34Moment,degree34MomentNumerator]
  ring

/-- The transformation is an identity for every real point, before restricting to the cube. -/
theorem compactPowerValue_bernstein (X T Z : ℝ) :
    compactPowerValue X T Z =
      ∑ i : Fin 35, ∑ j : Fin 35, ∑ k : Fin 35,
        compactBernsteinCoefficient i j k*bernsteinWeight 34 i X*
          bernsteinWeight 34 j T*bernsteinWeight 34 k Z := by
  let A := Fin 3 × Fin 3 × Fin 3
  let B := Fin 35 × Fin 35 × Fin 35
  have hmono (a : A) : X^(a.1:ℕ)*T^(a.2.1:ℕ)*Z^(a.2.2:ℕ) =
      ∑ b : B, degree34Moment a.1 b.1*degree34Moment a.2.1 b.2.1*
        degree34Moment a.2.2 b.2.2 * (bernsteinWeight 34 b.1 X*
          bernsteinWeight 34 b.2.1 T*bernsteinWeight 34 b.2.2 Z) := by
    rw [degree34Moment_expansion,degree34Moment_expansion,degree34Moment_expansion]
    rw [Finset.sum_mul_sum,Finset.sum_mul]
    simp_rw [Finset.sum_mul_sum]
    simp only [B,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have h : (∑ a : A, (compactPowerCoefficient a.1 a.2.1 a.2.2:ℝ)*
      (X^(a.1:ℕ)*T^(a.2.1:ℕ)*Z^(a.2.2:ℕ))) =
      ∑ b : B, (∑ a : A, (compactPowerCoefficient a.1 a.2.1 a.2.2:ℝ)*
        degree34Moment a.1 b.1*degree34Moment a.2.1 b.2.1*degree34Moment a.2.2 b.2.2)*
        (bernsteinWeight 34 b.1 X*bernsteinWeight 34 b.2.1 T*bernsteinWeight 34 b.2.2 Z) := by
    simp_rw [hmono,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  simpa only [A,B,Fintype.sum_prod_type,compactPowerValue,compactBernsteinCoefficient,mul_assoc] using h

end DittertRybin.Certificates.FourRowMinorant
