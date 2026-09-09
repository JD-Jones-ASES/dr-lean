import DR.Certificates.Gram
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators

/-!
# The four-row endpoint kernel and its rank-one estimate

The complementary-product definition is polynomial, so it remains defined
on every boundary marginal. The inverse-coordinate representation is used
only under an explicit positive-marginal hypothesis. The lower bound follows
from finite Cauchy--Schwarz; no matrix-inverse or spectral theorem is assumed.
-/

namespace DittertRybin
open scoped BigOperators
open Certificates

noncomputable def fourRowLeadingKernel (s : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if i = j then 1 else
    1 - 2 * ∏ k ∈ (Finset.univ.erase i).erase j, s k

noncomputable def fourRowReferenceQuadratic (s x : Fin 4 → ℝ) : ℝ :=
  (2 * ∏ i, s i) * (∑ i, (x i / s i) ^ 2) + (∑ i, x i) ^ 2

theorem fourRowLeadingKernel_symmetric (s : Fin 4 → ℝ) (i j : Fin 4) :
    fourRowLeadingKernel s i j = fourRowLeadingKernel s j i := by
  simp only [fourRowLeadingKernel, eq_comm, Finset.erase_right_comm]

theorem fourRowLeadingKernel_entry (s : Fin 4 → ℝ) (hs : ∀ i, s i ≠ 0) (i j : Fin 4) :
    fourRowLeadingKernel s i j =
      (if i = j then (2 * ∏ k, s k) / s i ^ 2 else 0) + 1 -
        (2 * ∏ k, s k) / (s i * s j) := by
  by_cases hij : i = j
  · subst j
    simp [fourRowLeadingKernel, pow_two]
  · have h1 := Finset.prod_erase_mul (Finset.univ.erase i) s
      (show j ∈ Finset.univ.erase i by simp [Ne.symm hij])
    have h2 := Finset.prod_erase_mul Finset.univ s (Finset.mem_univ i)
    have hp : (∏ k ∈ (Finset.univ.erase i).erase j, s k) * s j * s i = ∏ k, s k := by
      rw [h1, h2]
    simp only [fourRowLeadingKernel, if_neg hij, zero_add]
    field_simp [hs i, hs j]
    nlinarith [hp]

theorem fourRowLeadingKernel_quadratic (s x : Fin 4 → ℝ) (hs : ∀ i, s i ≠ 0) :
    quadraticValue (fourRowLeadingKernel s) x =
      fourRowReferenceQuadratic s x - (2 * ∏ i, s i) * (∑ i, x i / s i) ^ 2 := by
  unfold quadraticValue fourRowReferenceQuadratic
  simp_rw [fourRowLeadingKernel_entry s hs]
  simp [Fin.sum_univ_succ, Fin.prod_univ_succ]
  field_simp
  ring

/-- Cauchy--Schwarz in the diagonal-plus-one quadratic form, without matrix inverses. -/
theorem fourRow_rank_one_cauchy (s y : Fin 4 → ℝ) (hsum : ∑ i, s i = 1)
    (p : ℝ) (hp : 0 < p) :
    p * (∑ i, y i) ^ 2 ≤
      (4 - 1 / ((∑ i, s i ^ 2) + p)) *
        (p * (∑ i, y i ^ 2) + (∑ i, s i * y i) ^ 2) := by
  let q := ∑ i, s i ^ 2
  let d := q + p
  let z := ∑ i, s i * y i
  let v := fun i => 1 - s i / d
  have hq : 0 ≤ q := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hd : 0 < d := add_pos_of_nonneg_of_pos hq hp
  have hd0 := ne_of_gt hd
  let f : Option (Fin 4) → ℝ := fun i => i.elim (z ^ 2) (fun j => p * y j ^ 2)
  let g : Option (Fin 4) → ℝ := fun i => i.elim ((p / d) ^ 2) (fun j => p * v j ^ 2)
  let r : Option (Fin 4) → ℝ := fun i => i.elim (z * (p / d)) (fun j => p * y j * v j)
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := r) (f := f) (g := g)
    (fun i _ => by cases i <;> dsimp [f] <;> positivity)
    (fun i _ => by cases i <;> dsimp [g] <;> positivity)
    (fun i _ => by cases i <;> dsimp [r, f, g] <;> nlinarith)
  have hv : ∑ i, v i ^ 2 = 4 - 2 / d + q / d ^ 2 := by
    simp only [v, sub_sq, one_pow, div_pow, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.sum_div, ← Finset.mul_sum, hsum]
    dsimp [q]
    ring
  have hr : ∑ i, r i = p * ∑ i, y i := by
    have hy : (∑ i, p * y i * (s i / d)) = p * z / d := by
      calc
        _ = ∑ i, (p / d) * (s i * y i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = (p / d) * z := by rw [← Finset.mul_sum]
        _ = _ := by ring
    simp only [Fintype.sum_option, r, Option.elim, v, mul_sub, mul_one,
      Finset.sum_sub_distrib, hy, ← Finset.mul_sum]
    ring
  have hf : ∑ i, f i = p * (∑ i, y i ^ 2) + z ^ 2 := by
    simp [Fintype.sum_option, f, ← Finset.mul_sum, add_comm]
  have hg : ∑ i, g i = p * (4 - 1 / d) := by
    simp only [Fintype.sum_option, g, Option.elim, ← Finset.mul_sum, hv]
    dsimp [d]
    field_simp
    ring
  rw [hr, hf, hg] at h
  have hdiv := (mul_le_mul_iff_right₀ hp).mp (show
      p * (p * (∑ i, y i) ^ 2) ≤ p * ((4 - 1 / d) * (p * (∑ i, y i ^ 2) + z ^ 2)) by
    nlinarith [h])
  exact hdiv

theorem fourRowLeadingKernel_rank_one_lower (s x : Fin 4 → ℝ)
    (hs : ∀ i, 0 < s i) (hsum : ∑ i, s i = 1) :
    (1 / ((∑ i, s i ^ 2) + 2 * ∏ i, s i) - 3) * fourRowReferenceQuadratic s x ≤
      quadraticValue (fourRowLeadingKernel s) x := by
  have hs0 : ∀ i, s i ≠ 0 := fun i => ne_of_gt (hs i)
  have hp : 0 < 2 * ∏ i, s i := mul_pos (by norm_num) (Finset.prod_pos fun i _ => hs i)
  have h := fourRow_rank_one_cauchy s (fun i => x i / s i) hsum _ hp
  have hsumx : (∑ i, s i * (x i / s i)) = ∑ i, x i := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hs0 i]
  rw [hsumx] at h
  rw [fourRowLeadingKernel_quadratic s x hs0]
  unfold fourRowReferenceQuadratic
  nlinarith

end DittertRybin
