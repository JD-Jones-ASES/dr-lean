import DR.Square.CapacityUnivariate
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.BigOperators.Fin

/-!
# From split polynomials to the univariate capacity estimate

This module connects ordinary real polynomials to the explicit affine-factor
estimate. Padding by constant-one factors gives the ambient-degree factor
directly, so monotonicity of the sharp factors is unnecessary.
-/

open scoped BigOperators
open Finset Polynomial

namespace DittertRybin

/-- Appending constant-one factors preserves the represented function. -/
theorem affineProduct_append_constants {k d : ℕ} (a b : Fin k → ℝ) :
    affineProduct (Fin.append a (fun _ : Fin d => 0))
      (Fin.append b (fun _ : Fin d => 1)) = affineProduct a b := by
  funext t
  simp only [affineProduct, Fin.prod_univ_add, Fin.append_left, Fin.append_right,
    zero_mul, add_zero, Finset.prod_const_one, mul_one]

/-- Padding retains all nonnegativity conditions and permits any larger dimension. -/
theorem exists_affineProduct_padding {k n : ℕ} (hkn : k ≤ n) {a b : Fin k → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∃ a' b' : Fin n → ℝ, (∀ i, 0 ≤ a' i) ∧ (∀ i, 0 ≤ b' i) ∧
      affineProduct a' b' = affineProduct a b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkn
  refine ⟨Fin.append a (fun _ : Fin d => 0), Fin.append b (fun _ : Fin d => 1), ?_, ?_,
    affineProduct_append_constants a b⟩
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using ha j
    · intro j
      simp
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa using hb j
    · intro j
      simp

/-- Real splitting and nonpositive roots give a nonnegative affine representation.
Repeated roots are kept with multiplicity. The zero polynomial is allowed. -/
theorem exists_affineProduct_of_splits {p : ℝ[X]} (hs : p.Splits)
    (hr : ∀ r ∈ p.roots, r ≤ 0) {n : ℕ} (hdegree : p.natDegree ≤ n) :
    ∃ a b : Fin n → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, 0 ≤ b i) ∧
      (fun t => p.eval t) = fun t => p.leadingCoeff * affineProduct a b t := by
  classical
  let l := p.roots.toList
  let b : Fin l.length → ℝ := fun i => -l[i.1]
  have hb : ∀ i, 0 ≤ b i := by
    intro i
    exact neg_nonneg.mpr (hr _ (Multiset.mem_toList.mp (List.getElem_mem i.2)))
  have hk : l.length ≤ n := by
    simpa only [l, Multiset.length_toList, ← hs.natDegree_eq_card_roots] using hdegree
  obtain ⟨a', b', ha', hb', hpad⟩ := exists_affineProduct_padding hk
    (a := fun _ => 1) (b := b) (by intro i; norm_num) hb
  refine ⟨a', b', ha', hb', ?_⟩
  funext t
  rw [hpad, hs.eval_eq_prod_roots]
  congr 1
  calc
    (p.roots.map (fun r => t - r)).prod = ∏ i : Fin l.length, (t - l[i.1]) := by
      rw [Fin.prod_univ_fun_getElem, Multiset.prod_map_toList]
    _ = affineProduct (fun _ => 1) b t := by
      apply Finset.prod_congr rfl
      intro i hi
      dsimp [b]
      ring

/-- Nonnegative coefficients imply nonnegative evaluation on the nonnegative axis. -/
theorem polynomial_eval_nonneg {p : ℝ[X]} (hc : ∀ k, 0 ≤ p.coeff k)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ p.eval t := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hc k) (pow_nonneg ht k)

/-- A nonzero polynomial with nonnegative coefficients is positive at positive inputs. -/
theorem polynomial_eval_pos {p : ℝ[X]} (hc : ∀ k, 0 ≤ p.coeff k) (hp : p ≠ 0)
    {t : ℝ} (ht : 0 < t) : 0 < p.eval t := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum]
  apply Finset.sum_pos'
  · exact fun k _ => mul_nonneg (hc k) (pow_nonneg ht.le k)
  · refine ⟨p.natDegree, Polynomial.natDegree_mem_support_of_nonzero hp, ?_⟩
    exact mul_pos (lt_of_le_of_ne (hc _) (by simpa using (Polynomial.leadingCoeff_ne_zero.mpr hp).symm))
      (pow_pos ht _)

/-- Thus every real root is nonpositive; no separate sign assumption is needed. -/
theorem polynomial_roots_nonpos {p : ℝ[X]} (hc : ∀ k, 0 ≤ p.coeff k) :
    ∀ r ∈ p.roots, r ≤ 0 := by
  intro r hr
  by_contra! hpos
  have h := polynomial_eval_pos hc (Polynomial.ne_zero_of_mem_roots hr) hpos
  have hz := Polynomial.isRoot_of_mem_roots hr
  exact h.ne' hz

theorem scaledAffineProduct_capacity_le_deriv {n : ℕ} (hn : 2 ≤ n)
    {a b : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    {c : ℝ} (hc : 0 ≤ c) :
    capacityFactor n * univariateCapacity (fun t => c * affineProduct a b t) ≤
      deriv (fun t => c * affineProduct a b t) 0 := by
  rw [univariateCapacity_mul hc,
    deriv_const_mul _ (affineProduct_hasDerivAt_zero a b).differentiableAt]
  calc
    _ = c * (capacityFactor n * univariateCapacity (affineProduct a b)) := by ring
    _ ≤ c * deriv (affineProduct a b) 0 :=
      mul_le_mul_of_nonneg_left (affineProduct_capacity_le_deriv hn ha hb) hc

/-- Gurvits's univariate bound for an ordinary split real polynomial. The degree
may be below the ambient n, and the constant and zero polynomials are included. -/
theorem polynomial_capacity_le_deriv {p : ℝ[X]} (hs : p.Splits)
    (hc : ∀ k, 0 ≤ p.coeff k) {n : ℕ} (hn : 2 ≤ n) (hdegree : p.natDegree ≤ n) :
    capacityFactor n * univariateCapacity (fun t => p.eval t) ≤ p.derivative.eval 0 := by
  obtain ⟨a, b, ha, hb, hrep⟩ := exists_affineProduct_of_splits hs
    (polynomial_roots_nonpos hc) hdegree
  rw [← p.deriv, hrep]
  exact scaledAffineProduct_capacity_le_deriv hn ha hb (by simpa using hc p.natDegree)

end DittertRybin
