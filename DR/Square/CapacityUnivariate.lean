import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.Real.Pointwise
import Mathlib.Tactic

/-!
# The elementary one-variable step in Gurvits's capacity argument

The normalized product below represents a polynomial with positive constant
term and nonpositive real roots. Its capacity-to-derivative estimate follows
from AM–GM at a single explicitly chosen positive point.

Source: Leonid Gurvits, *Van der Waerden/Schrijver–Valiant like conjectures
and stable (aka hyperbolic) homogeneous polynomials: one theorem for all*,
Electronic Journal of Combinatorics 15 (2008), R66, Lemma 3.2;
https://arxiv.org/abs/0711.3496v2.

This module does not assume or assert multivariate stability closure or the
van der Waerden permanent inequality. Those remain separate proof obligations.
-/

open scoped BigOperators
open Finset Set

namespace DittertRybin

/-- Capacity of a real function in one variable, with the positive domain explicit. -/
noncomputable def univariateCapacity (f : ℝ → ℝ) : ℝ :=
  sInf (Set.range (fun t : {t : ℝ // 0 < t} => f t / t))

theorem univariateCapacity_le {f : ℝ → ℝ} (hf : ∀ t, 0 < t → 0 ≤ f t)
    {t : ℝ} (ht : 0 < t) : univariateCapacity f ≤ f t / t := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro x ⟨u, rfl⟩
    exact div_nonneg (hf u u.2) u.2.le
  · exact ⟨⟨t, ht⟩, rfl⟩

theorem le_univariateCapacity {f : ℝ → ℝ} {c : ℝ}
    (h : ∀ t, 0 < t → c ≤ f t / t) : c ≤ univariateCapacity f := by
  apply le_csInf
  · exact ⟨f 1 / 1, ⟨⟨1, by norm_num⟩, rfl⟩⟩
  · rintro x ⟨t, rfl⟩
    exact h t t.2

theorem univariateCapacity_nonneg {f : ℝ → ℝ}
    (hf : ∀ t, 0 < t → 0 ≤ f t) : 0 ≤ univariateCapacity f :=
  le_univariateCapacity fun t ht => div_nonneg (hf t ht) ht.le

/-- A normalized product of nonnegative-slope affine factors. -/
def normalizedProduct {n : ℕ} (a : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∏ i, (1 + a i * t)

theorem normalizedProduct_nonneg {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ normalizedProduct a t :=
  Finset.prod_nonneg fun i _ => add_nonneg (by norm_num) (mul_nonneg (ha i) ht)

theorem normalizedProduct_hasDerivAt_zero {n : ℕ} (a : Fin n → ℝ) :
    HasDerivAt (normalizedProduct a) (∑ i, a i) 0 := by
  have hfactor (i : Fin n) : HasDerivAt (fun t : ℝ => 1 + a i * t) (a i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (a i)).const_add 1
  convert! HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hfactor i) using 1
  simp

theorem normalizedProduct_deriv_zero {n : ℕ} (a : Fin n → ℝ) :
    deriv (normalizedProduct a) 0 = ∑ i, a i :=
  (normalizedProduct_hasDerivAt_zero a).deriv

/-- Ordinary finite AM–GM with a natural power, convenient for polynomial bounds. -/
theorem prod_le_arithMean_pow {n : ℕ} (hn : 0 < n) (z : Fin n → ℝ)
    (hz : ∀ i, 0 ≤ z i) : (∏ i, z i) ≤ ((∑ i, z i) / n) ^ n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hw : ∑ _ : Fin n, (n : ℝ)⁻¹ = 1 := by simp [hn0]
  have hgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : Fin n => (n : ℝ)⁻¹) z (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg n))
    hw (fun i _ => hz i)
  have hpow := pow_le_pow_left₀
    (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hz i) _)) hgm n
  rw [← Finset.prod_pow] at hpow
  simp only [Real.rpow_inv_natCast_pow (hz _) hn.ne'] at hpow
  rw [← Finset.mul_sum] at hpow
  simpa only [div_eq_mul_inv, mul_comm] using hpow

theorem normalizedProduct_le_mean_pow {n : ℕ} (hn : 0 < n) {a : Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) {t : ℝ} (ht : 0 ≤ t) :
    normalizedProduct a t ≤ (1 + (∑ i, a i) * t / n) ^ n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := prod_le_arithMean_pow hn (fun i => 1 + a i * t)
    (fun i => add_nonneg (by norm_num) (mul_nonneg (ha i) ht))
  have hmean : (∑ i : Fin n, (1 + a i * t)) / n = 1 + (∑ i, a i) * t / n := by
    simp [Finset.sum_add_distrib, ← Finset.sum_mul, add_div, hn0]
  simpa only [normalizedProduct, hmean] using h

/-- The sharp factor lost in one capacity-to-derivative step. -/
noncomputable def capacityFactor (n : ℕ) : ℝ :=
  (((n : ℝ) - 1) / n) ^ (n - 1)

theorem capacityFactor_pos {n : ℕ} (hn : 2 ≤ n) : 0 < capacityFactor n := by
  unfold capacityFactor
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  exact pow_pos (div_pos (by linarith) (by linarith)) _

/-- The explicit comparison point removes the need to find an infimum's minimizer. -/
theorem capacityFactor_at_comparison_point {n : ℕ} (hn : 2 ≤ n)
    {s : ℝ} (hs : 0 < s) :
    capacityFactor n *
      ((1 + s * ((n : ℝ) / (s * (n - 1))) / n) ^ n /
        ((n : ℝ) / (s * (n - 1)))) = s := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hnm0 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hs0 : s ≠ 0 := hs.ne'
  have hmean : 1 + s * ((n : ℝ) / (s * (n - 1))) / n = (n : ℝ) / (n - 1) := by
    field_simp
    ring
  rw [hmean]
  have hpow : ((n : ℝ) / (n - 1)) ^ n =
      ((n : ℝ) / (n - 1)) ^ (n - 1) * ((n : ℝ) / (n - 1)) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
      pow_succ ((n : ℝ) / (n - 1)) (n - 1)
  rw [hpow]
  have hinv : (((n : ℝ) - 1) / n) ^ (n - 1) *
      ((n : ℝ) / (n - 1)) ^ (n - 1) = 1 := by
    rw [← mul_pow]
    have hb : (((n : ℝ) - 1) / n) * ((n : ℝ) / (n - 1)) = 1 := by
      field_simp
    rw [hb, one_pow]
  unfold capacityFactor
  calc
    _ = ((((n : ℝ) - 1) / n) ^ (n - 1) * ((n : ℝ) / (n - 1)) ^ (n - 1)) *
        (((n : ℝ) / (n - 1)) / ((n : ℝ) / (s * (n - 1)))) := by ring
    _ = s := by rw [hinv]; field_simp

theorem univariateCapacity_one : univariateCapacity (fun _ : ℝ => 1) = 0 := by
  have hnon := univariateCapacity_nonneg (f := fun _ : ℝ => 1) (by intro t ht; norm_num)
  apply le_antisymm _ hnon
  by_contra! hpos
  have ht : 0 < 2 / univariateCapacity (fun _ : ℝ => 1) := div_pos (by norm_num) hpos
  have hbound := univariateCapacity_le (f := fun _ : ℝ => 1) (by intro t ht; norm_num) ht
  have heq : 1 / (2 / univariateCapacity (fun _ : ℝ => 1)) =
      univariateCapacity (fun _ : ℝ => 1) / 2 := by field_simp
  rw [heq] at hbound
  linarith

/-- Gurvits's sharp univariate estimate for a normalized product. Zero slopes,
including the constant polynomial, are allowed. -/
theorem normalizedProduct_capacity_bound {n : ℕ} (hn : 2 ≤ n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) :
    capacityFactor n * univariateCapacity (normalizedProduct a) ≤ ∑ i, a i := by
  have hs0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg fun i _ => ha i
  rcases hs0.eq_or_lt with hzero | hs
  · have hall : ∀ i, a i = 0 := by
      have hsum := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => ha i)).mp hzero.symm
      exact fun i => hsum i (Finset.mem_univ i)
    have hp : normalizedProduct a = fun _ : ℝ => 1 := by
      funext t
      simp [normalizedProduct, hall]
    rw [hp, univariateCapacity_one, mul_zero, hzero.symm]
  · let t : ℝ := n / ((∑ i, a i) * (n - 1))
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have ht : 0 < t := div_pos (by linarith) (mul_pos hs (by linarith))
    have hcap := univariateCapacity_le (f := normalizedProduct a)
      (fun u hu => normalizedProduct_nonneg ha hu.le) ht
    have hgm := normalizedProduct_le_mean_pow (by omega : 0 < n) ha ht.le
    calc
      _ ≤ capacityFactor n * (normalizedProduct a t / t) :=
        mul_le_mul_of_nonneg_left hcap (capacityFactor_pos hn).le
      _ ≤ capacityFactor n * ((1 + (∑ i, a i) * t / n) ^ n / t) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hgm ht.le)
          (capacityFactor_pos hn).le
      _ = ∑ i, a i := capacityFactor_at_comparison_point hn hs

/-- The right side of the normalized capacity bound is the actual derivative. -/
theorem normalizedProduct_capacity_le_deriv {n : ℕ} (hn : 2 ≤ n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) :
    capacityFactor n * univariateCapacity (normalizedProduct a) ≤
      deriv (normalizedProduct a) 0 := by
  rw [normalizedProduct_deriv_zero]
  exact normalizedProduct_capacity_bound hn ha

theorem univariateCapacity_mul {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    univariateCapacity (fun t => c * f t) = c * univariateCapacity f := by
  change (⨅ t : {t : ℝ // 0 < t}, c * f t / t) =
    c * ⨅ t : {t : ℝ // 0 < t}, f t / t
  rw [Real.mul_iInf_of_nonneg hc]
  simp only [mul_div_assoc]

/-- The one-variable homogeneous endpoint is its sole coefficient. -/
theorem univariateCapacity_linear {c : ℝ} (hc : 0 ≤ c) :
    univariateCapacity (fun t => c * t) = c := by
  apply le_antisymm
  · simpa using univariateCapacity_le (f := fun t => c * t)
      (fun t ht => mul_nonneg hc ht.le) (t := 1) (by norm_num)
  · apply le_univariateCapacity
    intro t ht
    simp [ht.ne']

/-- The zero-constant-term branch needs only the derivative limit from the right. -/
theorem univariateCapacity_le_deriv_of_zero {f : ℝ → ℝ} {d : ℝ}
    (hf : ∀ t, 0 < t → 0 ≤ f t) (hzero : f 0 = 0) (hd : HasDerivAt f d 0) :
    univariateCapacity f ≤ d := by
  have hlim : Filter.Tendsto (fun t : ℝ => f t / t) (nhdsWithin 0 (Ioi 0)) (nhds d) := by
    simpa [hzero, div_eq_mul_inv, mul_comm] using hd.tendsto_slope_zero_right
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact univariateCapacity_le hf ht

theorem capacityFactor_le_one {n : ℕ} (hn : 2 ≤ n) : capacityFactor n ≤ 1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply pow_le_one₀ (div_nonneg (by linarith) (by linarith))
  exact (div_le_one (by linarith)).mpr (by linarith)

/-- Scaling the positive-constant-term case preserves the sharp factor. -/
theorem scaledNormalizedProduct_capacity_le_deriv {n : ℕ} (hn : 2 ≤ n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) {c : ℝ} (hc : 0 ≤ c) :
    capacityFactor n * univariateCapacity (fun t => c * normalizedProduct a t) ≤
      deriv (fun t => c * normalizedProduct a t) 0 := by
  rw [univariateCapacity_mul hc,
    ((normalizedProduct_hasDerivAt_zero a).const_mul c).deriv]
  calc
    _ = c * (capacityFactor n * univariateCapacity (normalizedProduct a)) := by ring
    _ ≤ c * ∑ i, a i := mul_le_mul_of_nonneg_left (normalizedProduct_capacity_bound hn ha) hc

/-- A product representation that permits roots at zero and missing degree. -/
def affineProduct {n : ℕ} (a b : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∏ i, (b i + a i * t)

theorem affineProduct_nonneg {n : ℕ} {a b : Fin n → ℝ}
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ affineProduct a b t :=
  Finset.prod_nonneg fun i _ => add_nonneg (hb i) (mul_nonneg (ha i) ht)

theorem affineProduct_hasDerivAt_zero {n : ℕ} (a b : Fin n → ℝ) :
    HasDerivAt (affineProduct a b) (∑ i, (∏ j ∈ Finset.univ.erase i, b j) * a i) 0 := by
  have hfactor (i : Fin n) : HasDerivAt (fun t : ℝ => b i + a i * t) (a i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (a i)).const_add (b i)
  convert! HasDerivAt.fun_finsetProd (u := Finset.univ) (fun i _ => hfactor i) using 1
  simp

theorem affineProduct_eq_scaledNormalizedProduct {n : ℕ} {a b : Fin n → ℝ}
    (hb : ∀ i, b i ≠ 0) :
    affineProduct a b = fun t => (∏ i, b i) * normalizedProduct (fun i => a i / b i) t := by
  funext t
  simp only [affineProduct, normalizedProduct, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  field_simp [hb i]

/-- The elementary real-root factorization form of Gurvits's univariate lemma.
It covers zero constant terms, zero slopes, and the identically zero product. -/
theorem affineProduct_capacity_le_deriv {n : ℕ} (hn : 2 ≤ n)
    {a b : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    capacityFactor n * univariateCapacity (affineProduct a b) ≤
      deriv (affineProduct a b) 0 := by
  by_cases hz : affineProduct a b 0 = 0
  · have hcap : 0 ≤ univariateCapacity (affineProduct a b) :=
      univariateCapacity_nonneg fun t ht => affineProduct_nonneg ha hb ht.le
    calc
      _ ≤ 1 * univariateCapacity (affineProduct a b) :=
        mul_le_mul_of_nonneg_right (capacityFactor_le_one hn) hcap
      _ = univariateCapacity (affineProduct a b) := one_mul _
      _ ≤ deriv (affineProduct a b) 0 :=
        univariateCapacity_le_deriv_of_zero (fun t ht => affineProduct_nonneg ha hb ht.le)
          hz (affineProduct_hasDerivAt_zero a b).differentiableAt.hasDerivAt
  · have hb0 : ∀ i, b i ≠ 0 := by
      have hprod : (∏ i, b i) ≠ 0 := by simpa [affineProduct] using hz
      exact fun i => (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
    rw [affineProduct_eq_scaledNormalizedProduct hb0]
    exact scaledNormalizedProduct_capacity_le_deriv hn
      (fun i => div_nonneg (ha i) (hb i)) (Finset.prod_nonneg fun i _ => hb i)

end DittertRybin
