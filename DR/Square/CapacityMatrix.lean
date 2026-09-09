import DR.Definitions
import DR.Square.CapacityUnivariate
import Mathlib.Analysis.Convex.DoublyStochasticMatrix

/-!
# Initial capacity of a doubly stochastic matrix product

For a doubly stochastic matrix A, the product of its row linear forms has
capacity exactly one. Weighted AM–GM proves the lower bound, and the vector
of ones realizes the upper bound. All boundary zero entries are allowed.

This is the initial normalization in Gurvits's capacity proof; it does not
yet connect capacity to the permanent. See Gurvits (2008), arXiv:0711.3496v2,
and Laurent–Schrijver (2010), https://ir.cwi.nl/pub/16667/16667A.pdf.
-/

open scoped BigOperators
open Finset Set Matrix

namespace DittertRybin

/-- Capacity on strictly positive vectors, with the coordinate product denominator. -/
noncomputable def multivariateCapacity {n : ℕ} (f : (Fin n → ℝ) → ℝ) : ℝ :=
  sInf (Set.range (fun x : {x : Fin n → ℝ // ∀ i, 0 < x i} => f x / ∏ i, x.1 i))

theorem multivariateCapacity_le {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ∀ x, (∀ i, 0 < x i) → 0 ≤ f x) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) : multivariateCapacity f ≤ f x / ∏ i, x i := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro y ⟨u, rfl⟩
    exact div_nonneg (hf u u.2) (Finset.prod_pos (fun i _ => u.2 i)).le
  · exact ⟨⟨x, hx⟩, rfl⟩

theorem le_multivariateCapacity {n : ℕ} {f : (Fin n → ℝ) → ℝ} {c : ℝ}
    (h : ∀ x, (∀ i, 0 < x i) → c ≤ f x / ∏ i, x i) : c ≤ multivariateCapacity f := by
  apply le_csInf
  · exact ⟨f (fun _ => 1) / ∏ _ : Fin n, (1 : ℝ),
      ⟨⟨fun _ => 1, by intro i; norm_num⟩, rfl⟩⟩
  · rintro y ⟨x, rfl⟩
    exact h x x.2

/-- Product of row linear forms, evaluated at x. -/
def matrixProduct {n : ℕ} (A : Board n n) (x : Fin n → ℝ) : ℝ :=
  ∏ i, ∑ j, A i j * x j

theorem matrixProduct_nonneg {n : ℕ} {A : Board n n}
    (hA : ∀ i j, 0 ≤ A i j) {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    0 ≤ matrixProduct A x :=
  Finset.prod_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hx j)

/-- Weighted AM–GM and the column sums give the capacity lower bound pointwise. -/
theorem prod_le_matrixProduct_of_doublyStochastic {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) :
    (∏ i, x i) ≤ matrixProduct A x := by
  have hrow (i : Fin n) : (∏ j, (x j) ^ (A i j)) ≤ ∑ j, A i j * x j :=
    Real.geom_mean_le_arith_mean_weighted Finset.univ (fun j => A i j) x
      (fun j _ => nonneg_of_mem_doublyStochastic hA) (sum_row_of_mem_doublyStochastic hA i)
      (fun j _ => (hx j).le)
  have hprod := Finset.prod_le_prod
    (fun i (_ : i ∈ Finset.univ) =>
      Finset.prod_nonneg fun j _ => Real.rpow_nonneg (hx j).le _) (fun i _ => hrow i)
  have hid : (∏ i, ∏ j, (x j) ^ (A i j)) = ∏ j, x j := by
    rw [Finset.prod_comm]
    apply Finset.prod_congr rfl
    intro j hj
    rw [← Real.rpow_sum_of_pos (hx j), sum_col_of_mem_doublyStochastic hA j, Real.rpow_one]
  simpa only [hid, matrixProduct] using hprod

/-- The initial capacity is exactly one, including n=0 and zero matrix entries. -/
theorem matrixProduct_capacity_eq_one {n : ℕ} {A : Board n n}
    (hA : A ∈ doublyStochastic ℝ (Fin n)) :
    multivariateCapacity (matrixProduct A) = 1 := by
  apply le_antisymm
  · have h := multivariateCapacity_le (f := matrixProduct A)
      (fun x hx => matrixProduct_nonneg (fun i j => nonneg_of_mem_doublyStochastic hA)
        (fun i => (hx i).le)) (x := fun _ => 1) (by intro i; norm_num)
    simpa [matrixProduct, sum_row_of_mem_doublyStochastic hA] using h
  · apply le_multivariateCapacity
    intro x hx
    exact (one_le_div (Finset.prod_pos fun i _ => hx i)).mpr
      (prod_le_matrixProduct_of_doublyStochastic hA hx)

/-- Exact telescoping of the capacity losses. -/
theorem prod_capacityFactor (n : ℕ) :
    (∏ k ∈ Finset.range n, capacityFactor (k + 1)) = dittertConstant n := by
  induction n with
  | zero => simp [dittertConstant]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    rcases n.eq_zero_or_pos with rfl | hn
    · norm_num [dittertConstant, capacityFactor]
    · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      have hns0 : (n : ℝ) + 1 ≠ 0 := by positivity
      simp only [dittertConstant, capacityFactor,
        add_sub_cancel_right, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_succ, div_pow, pow_succ]
      field_simp

end DittertRybin
