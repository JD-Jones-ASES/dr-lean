import DR.Rectangular.FourRowFiniteSeedKernel

/-! Evaluation of the exact kernel coefficients on the actual full compressed matrices. -/

namespace DittertRybin
open scoped BigOperators
open MvPolynomial Certificates
noncomputable section

theorem fourRowFiniteSeedFullPower_eval (h : Fin 391 → Fin 5 → ℚ)
    {a : ℕ} (ha : 5 ≤ a) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (s : Fin 10) (i j : Fin (fourRowFiniteSeedFullSize s)) :
    rationalEval (fun _ => u) (powerPolynomial (fourRowFiniteSeedFullPower h a s i j)) =
      fourRowFiniteDenominator a u * fourRowFiniteSeedFullMatrix s ((a : ℝ)/u)
        (fun key => fourRowFiniteNumeratorValue h (fourRowFiniteRoleLookup key) u) i j := by
  have hc : 1 ≤ fourRowFiniteSeedColumns s := (fourRowFiniteSeed_counts s).2.2.2.1
  unfold fourRowFiniteSeedFullPower
  rw [fourRowFiniteTrivialPower_polynomial]
  change rationalEval (fun _ => u)
    (fourRowFiniteTrivialPolynomial _ _ a (fourRowFiniteFamilyRolePolynomial h) _ _ _) = _
  rw [fourRowFiniteTrivialPolynomial_eval ha hu hu1]
  simp_rw [fourRowFiniteFamilyRolePolynomial_eval]
  simp only [Nat.sub_add_cancel hc]
  rfl

theorem fourRowFiniteSeedKernelPower_eval (h : Fin 391 → Fin 5 → ℚ)
    {a : ℕ} (ha : 5 ≤ a) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (s : Fin 10) (i : Fin (fourRowFiniteSeedFullSize s)) :
    rationalEval (fun _ => u) (powerPolynomial (fourRowFiniteSeedKernelPower h a s i)) =
      u*fourRowFiniteDenominator a u *
        ∑ j : Fin (fourRowFiniteSeedFullSize s),
          fourRowFiniteSeedFullMatrix s ((a : ℝ)/u)
            (fun key => fourRowFiniteNumeratorValue h (fourRowFiniteRoleLookup key) u) i j *
            fourRowFiniteSeedWeight s ((a : ℝ)/u) j.val := by
  rw [fourRowFiniteSeedKernelPower_polynomial]
  simp only [rationalEval, eval₂_sum, eval₂_mul, eval₂_add, eval₂_C, eval₂_X, Rat.coe_castHom]
  change (∑ j : Fin (fourRowFiniteSeedFullSize s),
    ((fourRowFiniteSeedAffineConstant a s j.val : ℝ)+(fourRowFiniteSeedAffineLinear s j.val : ℝ)*u)*
      rationalEval (fun _ => u) (powerPolynomial (fourRowFiniteSeedFullPower h a s i j))) = _
  simp_rw [fourRowFiniteSeedAffine_eq a s _ u hu.ne', fourRowFiniteSeedFullPower_eval h ha hu hu1]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A complete exact coefficient gate yields the actual full weighted kernel. -/
theorem fourRowFiniteSeedFullMatrix_kernel_of_coefficients (h : Fin 391 → Fin 5 → ℚ)
    {a : ℕ} (ha : 5 ≤ a) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (s : Fin 10)
    (hcoeff : ∀ i d, fourRowFiniteSeedKernelPower h a s i d = 0) :
    (fourRowFiniteSeedFullMatrix s ((a : ℝ)/u)
      (fun key => fourRowFiniteNumeratorValue h (fourRowFiniteRoleLookup key) u)).mulVec
        (fun j => fourRowFiniteSeedWeight s ((a : ℝ)/u) j.val) = 0 := by
  funext i
  have he := fourRowFiniteSeedKernelPower_eval h ha hu hu1 s i
  have hz : rationalEval (fun _ => u)
      (powerPolynomial (fourRowFiniteSeedKernelPower h a s i)) = 0 := by
    simp [powerPolynomial, hcoeff, rationalEval]
  rw [hz] at he
  have hD := fourRowFiniteDenominator_pos (a := (a : ℝ)) (u := u) (by exact_mod_cast ha) hu1
  have hs := (mul_eq_zero.mp he.symm).resolve_left (mul_ne_zero hu.ne' hD.ne')
  simpa only [Matrix.mulVec, dotProduct, Pi.zero_apply] using hs

theorem fourRowFiniteSeedWeight_pos (s : Fin 10) {N : ℝ} (hN : 3 < N) (j : ℕ) :
    0 < fourRowFiniteSeedWeight s N j := by
  have hr : (fourRowFiniteSeedRows s : ℝ) ≤ 3 := by
    exact_mod_cast (fourRowFiniteSeed_counts s).2.2.1
  have hc : (fourRowFiniteSeedColumns s : ℝ) ≤ 3 := by
    exact_mod_cast (fourRowFiniteSeed_counts s).2.2.2.2
  unfold fourRowFiniteSeedWeight
  apply mul_pos
  · unfold fourRowFiniteSeedRowWeight
    split_ifs
    · push_cast
      linarith
    · norm_num
  · split_ifs <;> linarith

end
end DittertRybin
