import DR.Rook
import DR.ElementarySymmetricBoundsNewton
import DR.ElementarySymmetricBoundsSequence
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.FunProp

/-! The canonical subset sums as coefficients of the real-rooted product. -/

namespace DittertRybin
open scoped BigOperators
open Polynomial

theorem elementarySymmetric_eq_powerset_sum {d : ℕ} (x : Fin d → ℝ) (k : ℕ) :
    elementarySymmetric x k =
      ∑ S ∈ (Finset.univ : Finset (Fin d)).powersetCard k, ∏ i ∈ S, x i := by
  classical
  let e := Set.powersetCard.ofFinEmbEquiv (n := k) (I := Fin d)
  have he : elementarySymmetric x k =
      ∑ S : Set.powersetCard (Fin d) k, ∏ i ∈ S.val, x i := by
    rw [elementarySymmetric,← e.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro S hS
    change (∏ i : Fin k, x (S.val.orderEmbOfFin S.prop i)) = _
    exact ((S.val.orderIsoOfFin S.prop).toEquiv.prod_comp (fun i : S.val => x i)).trans
      (Finset.prod_coe_sort S.val x)
  rw [he]
  exact (Finset.sum_subtype ((Finset.univ : Finset (Fin d)).powersetCard k)
    (by intro S; simp) (fun S => ∏ i ∈ S, x i)).symm

noncomputable def elementaryRootPolynomial {d : ℕ} (x : Fin d → ℝ) : ℝ[X] :=
  ∏ i, (X+C (x i))

theorem elementaryRootPolynomial_monic {d : ℕ} (x : Fin d → ℝ) :
    (elementaryRootPolynomial x).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_add_C (x i))

theorem elementaryRootPolynomial_natDegree {d : ℕ} (x : Fin d → ℝ) :
    (elementaryRootPolynomial x).natDegree = d := by
  rw [elementaryRootPolynomial,Polynomial.natDegree_prod_of_monic _ _
    (fun i _ => Polynomial.monic_X_add_C (x i))]
  simp

theorem elementaryRootPolynomial_splits {d : ℕ} (x : Fin d → ℝ) :
    (elementaryRootPolynomial x).Splits := by
  apply Polynomial.Splits.prod
  intro i hi
  exact Polynomial.Splits.of_natDegree_le_one (by simp)

theorem elementaryRootPolynomial_coeff {d k : ℕ} (x : Fin d → ℝ) (hk : k ≤ d) :
    (elementaryRootPolynomial x).coeff (d-k) = elementarySymmetric x k := by
  rw [elementaryRootPolynomial,Finset.prod_X_add_C_coeff _ _ (by simp)]
  simp only [Finset.card_univ,Fintype.card_fin,Nat.sub_sub_self hk]
  exact (elementarySymmetric_eq_powerset_sum x k).symm

noncomputable def elementaryMean {d : ℕ} (x : Fin d → ℝ) (k : ℕ) : ℝ :=
  elementarySymmetric x k / (d.choose k:ℝ)

theorem elementaryMean_eq_normalized_coefficient {d k : ℕ} (x : Fin d → ℝ) (hk : k ≤ d) :
    elementaryMean x k = normalizedPolynomialCoefficient (elementaryRootPolynomial x) (d-k) := by
  rw [normalizedPolynomialCoefficient,elementaryRootPolynomial_natDegree,
    elementaryRootPolynomial_coeff x hk,Nat.choose_symm hk]
  rfl

theorem elementarySymmetric_pos {d k : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 < x i) (hk : k ≤ d) : 0 < elementarySymmetric x k := by
  have : Nonempty (Fin k ↪o Fin d) := ⟨OrderEmbedding.ofStrictMono
    (fun i : Fin k => (⟨i.val,i.isLt.trans_le hk⟩ : Fin d)) (by intro i j hij; exact hij)⟩
  exact Finset.sum_pos (fun e _ => Finset.prod_pos fun i _ => hx (e i)) Finset.univ_nonempty

theorem elementaryMean_pos {d k : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 < x i) (hk : k ≤ d) : 0 < elementaryMean x k := by
  exact div_pos (elementarySymmetric_pos hx hk) (by exact_mod_cast Nat.choose_pos hk)

theorem elementaryMean_zero {d : ℕ} (x : Fin d → ℝ) : elementaryMean x 0 = 1 := by
  rw [elementaryMean,elementarySymmetric_eq_powerset_sum]
  simp

/-- The normalized Newton inequality for the original canonical elementary sums. -/
theorem elementaryMean_newton {d : ℕ} (x : Fin d → ℝ) {j : ℕ} (hj : j+2 ≤ d) :
    elementaryMean x j * elementaryMean x (j+2) ≤ elementaryMean x (j+1)^2 := by
  have h := normalizedCoefficient_newton (elementaryRootPolynomial_splits x)
    (j := d-(j+2)) (by rw [elementaryRootPolynomial_natDegree]; omega)
  have h1 : d-(j+2)+1 = d-(j+1) := by omega
  have h2 : d-(j+2)+2 = d-j := by omega
  rw [h1,h2,← elementaryMean_eq_normalized_coefficient x (show j+2 ≤ d from hj),
    ← elementaryMean_eq_normalized_coefficient x (show j+1 ≤ d by omega),
    ← elementaryMean_eq_normalized_coefficient x (show j ≤ d by omega)] at h
  simpa only [mul_comm] using h

theorem elementaryMean_maclaurin_two_pos {d k : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 < x i) (hk : 2 ≤ k) (hkd : k ≤ d) :
    elementaryMean x k^2 ≤ elementaryMean x 2^k :=
  positive_newton_power_bound (elementaryMean x) (fun _j hj => elementaryMean_pos hx hj)
    (elementaryMean_zero x) (fun _j hj => elementaryMean_newton x hj) hk hkd

/-- Maclaurin's second-order comparison includes every zero-coordinate boundary. -/
theorem elementaryMean_maclaurin_two {d k : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hk : 2 ≤ k) (hkd : k ≤ d) :
    elementaryMean x k^2 ≤ elementaryMean x 2^k := by
  have hc (j : ℕ) : Continuous (fun t : ℝ => elementaryMean (fun i => x i+t) j) := by
    unfold elementaryMean elementarySymmetric
    fun_prop
  have hl := ((hc k).pow 2).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ _)
  have hr := ((hc 2).pow k).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ _)
  have h := le_of_tendsto_of_tendsto hl hr (show
      ∀ᶠ t in nhdsWithin (0:ℝ) (Set.Ioi 0),
        elementaryMean (fun i => x i+t) k^2 ≤ elementaryMean (fun i => x i+t) 2^k from by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact elementaryMean_maclaurin_two_pos (fun i => add_pos_of_nonneg_of_pos (hx i) ht) hk hkd)
  simpa only [Pi.pow_apply,add_zero] using h

end DittertRybin
