import DR.Square.CapacityBound

/-!
# Matrix-specific first-deletion capacity lower bound

This is the two weighted AM–GM steps in Laurent–Schrijver (2010),
Corollary 1d, equation (39), https://ir.cwi.nl/pub/16667/16667A.pdf.
Zero row remainders are treated before division; `0^0 = 1` is retained.
-/

open scoped BigOperators
open Finset Set Matrix

namespace DittertRybin

private theorem prod_erase_eq_prod_ite {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (k : ι) :
    (∏ i ∈ Finset.univ.erase k, f i) = ∏ i, if i = k then 1 else f i := by
  calc
    _ = ∏ i ∈ Finset.univ.erase k, if i = k then 1 else f i := by
      apply Finset.prod_congr rfl
      intro i hi
      simp [(Finset.mem_erase.mp hi).1]
    _ = _ := Finset.prod_subset (Finset.erase_subset _ _) (by
      intro i hi hnot
      have hik : i = k := by simpa using hnot
      simp [hik])

/-- The first AM–GM step, valid even when some bases or weights vanish. -/
theorem weighted_deleted_product_lower_bound {m : ℕ} {a s : Fin m → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hsum : ∑ i, a i = 1) (hs : ∀ i, 0 ≤ s i) :
    (∏ i, (s i) ^ (1 - a i)) ≤
      ∑ k, a k * ∏ i ∈ Finset.univ.erase k, s i := by
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ a
    (fun k => ∏ i ∈ Finset.univ.erase k, s i)
    (fun k _ => ha k) hsum (fun k _ => Finset.prod_nonneg fun i _ => hs i)
  have heq : (∏ k, (∏ i ∈ Finset.univ.erase k, s i) ^ a k) =
      ∏ i, s i ^ (1 - a i) := by
    simp_rw [← Real.finsetProd_rpow _ _ (fun i _ => hs i)]
    simp_rw [prod_erase_eq_prod_ite]
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro i hi
    have hsum' : ∑ k : Fin m, (if i = k then 0 else a k) = 1 - a i := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hsum
      have he : (∑ k : Fin m, if i = k then 0 else a k) =
          ∑ k ∈ Finset.univ.erase i, a k := by
        simp [Finset.sum_ite, eq_comm, ← Finset.filter_ne']
      rw [he]
      linarith
    have hexp : (∏ k : Fin m, if i = k then 1 else s i ^ a k) =
        ∏ k : Fin m, s i ^ (if i = k then 0 else a k) := by
      apply Finset.prod_congr rfl
      intro k hk
      split_ifs <;> simp
    rw [hexp, ← Real.rpow_sum_of_nonneg (hs i) (fun k _ => by split_ifs <;> simp [ha]), hsum']
  rw [heq] at h
  exact h

/-- Weighted row normalization, with total weight zero handled explicitly. -/
theorem row_rpow_weighted_lower_bound {m : ℕ} {w x : Fin m → ℝ}
    (hw : ∀ j, 0 ≤ w j) (hx : ∀ j, 0 < x j) {b : ℝ}
    (hb : ∑ j, w j = b) :
    b ^ b * ∏ j, (x j) ^ (w j) ≤ (∑ j, w j * x j) ^ b := by
  have hb0 : 0 ≤ b := hb ▸ Finset.sum_nonneg (fun j _ => hw j)
  by_cases hzero : b = 0
  · have hwzero : ∀ j, w j = 0 := by
      intro j
      have hle := Finset.single_le_sum (fun k _ => hw k) (Finset.mem_univ j)
      rw [hb, hzero] at hle
      exact le_antisymm hle (hw j)
    simp [hzero, hwzero]
  have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hzero)
  have hwsum : ∑ j, w j / b = 1 := by rw [← Finset.sum_div, hb, div_self hzero]
  have hmean := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun j => w j / b) x (fun j _ => div_nonneg (hw j) hb0) hwsum (fun j _ => (hx j).le)
  have hpow := Real.rpow_le_rpow
    (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hx j).le _) hmean hb0
  have hleft : (∏ j, (x j) ^ (w j / b)) ^ b = ∏ j, (x j) ^ (w j) := by
    rw [← Real.finsetProd_rpow _ _ (fun j _ => Real.rpow_nonneg (hx j).le _)]
    apply Finset.prod_congr rfl
    intro j hj
    rw [← Real.rpow_mul (hx j).le, div_mul_cancel₀ _ hzero]
  have hright : ∑ j, w j * x j = b * ∑ j, (w j / b) * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    field_simp
  rw [hleft] at hpow
  rw [hright, Real.mul_rpow hb0 (Finset.sum_nonneg fun j _ =>
    mul_nonneg (div_nonneg (hw j) hb0) (hx j).le)]
  exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hb0 _)

theorem capacityReduce_matrixProduct_eval {n : ℕ} (A : Board (n + 1) (n + 1))
    (x : Fin n → ℝ) :
    (capacityReduce (matrixProductPolynomial A)).eval x =
      ∑ k, A k 0 * ∏ i ∈ Finset.univ.erase k, ∑ j : Fin n, A i j.succ * x j := by
  rw [capacityReduce_eval, ← Polynomial.deriv]
  have heq : (fun t => (singleVariableSlice (matrixProductPolynomial A) 0 (Fin.cons 1 x)).eval t) =
      affineProduct (fun i => A i 0) (fun i => ∑ j : Fin n, A i j.succ * x j) := by
    funext t
    rw [singleVariableSlice_zero_eval, matrixProductPolynomial_eval]
    simp [matrixProduct, affineProduct, Fin.sum_univ_succ, add_comm]
  rw [heq, (affineProduct_hasDerivAt_zero _ _).deriv]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The first deletion has the matrix-specific entropy-product lower bound.
This includes entries equal to one, hence zero row remainders. -/
theorem matrixProduct_first_deletion_capacity {n : ℕ}
    {A : Board (n + 1) (n + 1)} (hA : A ∈ doublyStochastic ℝ (Fin (n + 1))) :
    (∏ i, (1 - A i 0) ^ (1 - A i 0)) ≤
      multivariateCapacity (fun x => (capacityReduce (matrixProductPolynomial A)).eval x) := by
  have ha (i j : Fin (n + 1)) : 0 ≤ A i j := nonneg_of_mem_doublyStochastic hA
  have hrem (i : Fin (n + 1)) : ∑ j : Fin n, A i j.succ = 1 - A i 0 := by
    have h := sum_row_of_mem_doublyStochastic hA i
    rw [Fin.sum_univ_succ] at h
    linarith
  apply le_multivariateCapacity
  intro x hx
  have hrow (i : Fin (n + 1)) :=
    row_rpow_weighted_lower_bound (fun j => ha i j.succ) hx (hrem i)
  have hprod := Finset.prod_le_prod (s := Finset.univ)
    (fun i _ => mul_nonneg (Real.rpow_nonneg (sub_nonneg.mpr (le_one_of_mem_doublyStochastic hA)) _)
      (Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hx j).le _))
    (fun i _ => hrow i)
  have hid : (∏ i : Fin (n + 1), (1 - A i 0) ^ (1 - A i 0) *
      ∏ j : Fin n, (x j) ^ (A i j.succ)) =
        (∏ i, (1 - A i 0) ^ (1 - A i 0)) * ∏ j, x j := by
    rw [Finset.prod_mul_distrib, Finset.prod_comm]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [← Real.rpow_sum_of_pos (hx j), sum_col_of_mem_doublyStochastic hA j.succ, Real.rpow_one]
  rw [hid] at hprod
  have hdel := weighted_deleted_product_lower_bound (fun i => ha i 0)
    (sum_col_of_mem_doublyStochastic hA 0)
    (fun i => Finset.sum_nonneg (s := Finset.univ) fun j _ => mul_nonneg (ha i j.succ) (hx j).le)
  rw [le_div_iff₀ (Finset.prod_pos fun j _ => hx j), capacityReduce_matrixProduct_eval]
  exact hprod.trans hdel

/-- Equality in the permanent bound forces the first-deletion capacity to be
at most the corresponding loss factor; this uses the proved lower bound in
the smaller dimension. -/
theorem first_deletion_capacity_le_of_permanent_eq {n : ℕ}
    {A : Board (n + 1) (n + 1)} (hA : A ∈ doublyStochastic ℝ (Fin (n + 1)))
    (heq : A.permanent = dittertConstant (n + 1)) :
    multivariateCapacity (fun x => (capacityReduce (matrixProductPolynomial A)).eval x) ≤
      capacityFactor (n + 1) := by
  have hhom := matrixProductPolynomial_isHomogeneous A
  have hc := matrixProductPolynomial_nonnegative
    (fun i j => nonneg_of_mem_doublyStochastic hA (i := i) (j := j))
  have hs : matrixProductPolynomial A = 0 ∨ HStable (matrixProductPolynomial A) :=
    Or.inr (matrixProductPolynomial_hStable_of_doublyStochastic hA)
  have h := homogeneous_capacity_bound (capacityReduce_isHomogeneous hhom)
    (capacityReduce_nonnegative hc) (capacityReduce_zero_or_hStable hhom hc hs)
  rw [capacityReduce_squarefree_coefficient, matrixProductPolynomial_squarefree_coefficient,
    heq, ← dittertConstant_mul_capacityFactor] at h
  have hpos : 0 < dittertConstant n := by
    cases n with
    | zero => norm_num [dittertConstant]
    | succ n => unfold dittertConstant; positivity
  exact (mul_le_mul_iff_right₀ hpos).mp (by simpa [mul_comm] using h)

end DittertRybin
