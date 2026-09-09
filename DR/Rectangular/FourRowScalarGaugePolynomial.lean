import DR.Rectangular.FourRowGauge
import Mathlib.Data.Fin.Tuple.Sort

/-! The symmetric degree-seven scalar gauge polynomial and its exact normalization. -/

namespace DittertRybin
open scoped BigOperators

noncomputable def fourRowGaugeHomogeneous (r : Fin 4 → ℝ) : ℝ :=
  2*(3/32)*(∑ i, r i)^7 - 2*(∑ i, r i)^3*(∑ i, r i*fourRowGaugeCollision r i) -
    ∑ i, r i*(fourRowGaugeCollision r i-(3/32)*(∑ j, r j)^3)^2

noncomputable def fourRowGaugeHomogeneousVariance (r : Fin 4 → ℝ) : ℝ :=
  ∑ i, (r i-(∑ j, r j)/4)^2

/-- The omitted-three-coordinate definition equals the full-moment expression. -/
theorem fourRowGaugeCollision_moments (r : Fin 4 → ℝ) (i : Fin 4) :
    fourRowGaugeCollision r i =
      ((∑ j, r j)-r i)*((∑ j, r j^2)-r i^2)-((∑ j, r j^3)-r i^3) := by
  let S := Finset.univ.erase i
  let t := ∑ j ∈ S, r j
  have hother (j : Fin 4) (hj : j ∈ S) : (∑ k ∈ S.erase j, r k) = t-r j := by
    have h := Finset.sum_erase_add S r hj
    change (∑ k ∈ S.erase j, r k)+r j = t at h
    linarith
  have hg : fourRowGaugeCollision r i = t*(∑ j ∈ S, r j^2)-(∑ j ∈ S, r j^3) := by
    calc
      fourRowGaugeCollision r i = ∑ j ∈ S, r j^2*(t-r j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← Finset.mul_sum,hother j hj]
      _ = _ := by
        simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,pow_succ]
        ring
  have h1 : (∑ j ∈ S, r j) = (∑ j, r j)-r i := by
    have h := Finset.sum_erase_add Finset.univ r (Finset.mem_univ i)
    change (∑ j ∈ S, r j)+r i = ∑ j, r j at h
    linarith
  have h2 : (∑ j ∈ S, r j^2) = (∑ j, r j^2)-r i^2 := by
    have h := Finset.sum_erase_add Finset.univ (fun j => r j^2) (Finset.mem_univ i)
    change (∑ j ∈ S, r j^2)+r i^2 = ∑ j, r j^2 at h
    linarith
  have h3 : (∑ j ∈ S, r j^3) = (∑ j, r j^3)-r i^3 := by
    have h := Finset.sum_erase_add Finset.univ (fun j => r j^3) (Finset.mem_univ i)
    change (∑ j ∈ S, r j^3)+r i^3 = ∑ j, r j^3 at h
    linarith
  dsimp only [t] at hg
  rw [h1,h2,h3] at hg
  exact hg

theorem fourRowGaugeCollision_permute (r : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) (i : Fin 4) :
    fourRowGaugeCollision (r ∘ e) i = fourRowGaugeCollision r (e i) := by
  rw [fourRowGaugeCollision_moments,fourRowGaugeCollision_moments]
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp e r, Equiv.sum_comp e (fun j => r j^2), Equiv.sum_comp e (fun j => r j^3)]

theorem fourRowGaugeHomogeneous_permute (r : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) :
    fourRowGaugeHomogeneous (r ∘ e) = fourRowGaugeHomogeneous r := by
  unfold fourRowGaugeHomogeneous
  simp_rw [fourRowGaugeCollision_permute, Function.comp_apply]
  rw [Equiv.sum_comp e r, Equiv.sum_comp e (fun i => r i*fourRowGaugeCollision r i),
    Equiv.sum_comp e (fun i => r i*(fourRowGaugeCollision r i-(3/32)*(∑ j, r j)^3)^2)]

theorem fourRowGaugeHomogeneousVariance_permute (r : Fin 4 → ℝ) (e : Equiv.Perm (Fin 4)) :
    fourRowGaugeHomogeneousVariance (r ∘ e) = fourRowGaugeHomogeneousVariance r := by
  unfold fourRowGaugeHomogeneousVariance
  simp only [Function.comp_apply]
  rw [Equiv.sum_comp e r, Equiv.sum_comp e (fun i => (r i-(∑ j, r j)/4)^2)]

theorem fourRowGaugeHomogeneousVariance_probability (r : Fin 4 → ℝ) (hs : ∑ i, r i = 1) :
    fourRowGaugeHomogeneousVariance r = fourRowMarginalVariance r := by
  simp only [fourRowGaugeHomogeneousVariance,hs,fourRowMarginalVariance]

end DittertRybin
