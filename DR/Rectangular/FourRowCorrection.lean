import DR.Rectangular.FourRowKernelRegion
import DR.Definitions
import Mathlib.Algebra.BigOperators.Fin

/-!
# The exact remaining-column correction

The off-diagonal entries are the actual complementary two-row inner
products. Their row sums are bounded by one third of the column square
mass. This gives the signed quadratic lower bound needed in the averaging
kernel, including zero entries and zero columns.
-/

namespace DittertRybin
open scoped BigOperators
open Certificates

set_option maxHeartbeats 4000000

noncomputable def fourRowColumnComplement (v : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => if i = j then 0 else ∏ r ∈ (Finset.univ.erase i).erase j, v r

noncomputable def fourRowColumnSquareMass {n : ℕ} (T : Board 4 n) : ℝ :=
  ∑ j, colSum T j ^ 2

noncomputable def fourRowComplementCorrection {n : ℕ} (T : Board 4 n) :
    Matrix (Fin 4) (Fin 4) ℝ := fun i h =>
  ∑ j, fourRowColumnComplement (fun r => T r j) i h

noncomputable def fourRowBlendKernel {n : ℕ} (T : Board 4 n) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => (totalMass T ^ 2 - fourRowColumnSquareMass T) / 2 -
    fourRowColumnComplement (rowSum T) i j + fourRowComplementCorrection T i j

theorem fourRowColumnComplement_symmetric (v : Fin 4 → ℝ) (i j : Fin 4) :
    fourRowColumnComplement v i j = fourRowColumnComplement v j i := by
  simp only [fourRowColumnComplement, eq_comm, Finset.erase_right_comm]

theorem fourRowColumnComplement_nonneg (v : Fin 4 → ℝ) (hv : ∀ i, 0 ≤ v i) (i j : Fin 4) :
    0 ≤ fourRowColumnComplement v i j := by
  unfold fourRowColumnComplement
  split_ifs
  · exact le_rfl
  · exact Finset.prod_nonneg fun r _ => hv r

theorem fourRowColumnComplement_scale (v : Fin 4 → ℝ) (c : ℝ) (i j : Fin 4) :
    fourRowColumnComplement (fun r => c * v r) i j = c ^ 2 * fourRowColumnComplement v i j := by
  by_cases hij : i = j
  · simp [fourRowColumnComplement, hij]
  · have hj : j ∈ Finset.univ.erase i := by simp [Ne.symm hij]
    have hcard : ((Finset.univ.erase i).erase j).card = 2 := by
      rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i)]
      rfl
    simp only [fourRowColumnComplement, if_neg hij, Finset.prod_mul_distrib,
      Finset.prod_const, hcard]

theorem fourRowColumnComplement_row_bound (v : Fin 4 → ℝ) (hv : ∀ i, 0 ≤ v i) (i : Fin 4) :
    ∑ j, fourRowColumnComplement v i j ≤ (∑ j, v j) ^ 2 / 3 := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  have hi : ∀ i : Fin 4, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by decide
  rcases hi i with rfl | rfl | rfl | rfl <;> simp only [Fin.sum_univ_four]
  all_goals norm_num [fourRowColumnComplement, hu,
    Finset.sum_insert, Finset.prod_insert, Finset.erase_insert, Finset.erase_insert_of_ne,
    Finset.erase_singleton, Fin.ext_iff]
  all_goals nlinarith [sq_nonneg (v 0-v 1), sq_nonneg (v 0-v 2), sq_nonneg (v 0-v 3),
    sq_nonneg (v 1-v 2), sq_nonneg (v 1-v 3), sq_nonneg (v 2-v 3),
    mul_nonneg (hv 0) (hv 1), mul_nonneg (hv 0) (hv 2), mul_nonneg (hv 0) (hv 3),
    mul_nonneg (hv 1) (hv 2), mul_nonneg (hv 1) (hv 3), mul_nonneg (hv 2) (hv 3)]

theorem fourRowComplementCorrection_nonneg {n : ℕ} (T : Board 4 n)
    (hT : ∀ i j, 0 ≤ T i j) (i j : Fin 4) : 0 ≤ fourRowComplementCorrection T i j :=
  Finset.sum_nonneg fun c _ => fourRowColumnComplement_nonneg _ (fun r => hT r c) i j

theorem fourRowComplementCorrection_symmetric {n : ℕ} (T : Board 4 n) (i j : Fin 4) :
    fourRowComplementCorrection T i j = fourRowComplementCorrection T j i := by
  unfold fourRowComplementCorrection
  simp_rw [fourRowColumnComplement_symmetric _ i j]

theorem fourRowComplementCorrection_row_bound {n : ℕ} (T : Board 4 n)
    (hT : ∀ i j, 0 ≤ T i j) (i : Fin 4) :
    ∑ h, fourRowComplementCorrection T i h ≤ fourRowColumnSquareMass T / 3 := by
  unfold fourRowComplementCorrection
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ j, (∑ r, T r j) ^ 2 / 3 := Finset.sum_le_sum fun j _ =>
      fourRowColumnComplement_row_bound _ (fun r => hT r j) i
    _ = _ := by simp only [← Finset.sum_div, fourRowColumnSquareMass, colSum]

/-- An entrywise nonnegative symmetric matrix has a lower quadratic bound by its row cap. -/
theorem fourRow_symmetric_row_lower (H : Matrix (Fin 4) (Fin 4) ℝ)
    (hH : ∀ i j, 0 ≤ H i j) (hsym : ∀ i j, H i j = H j i) (a : ℝ)
    (hrows : ∀ i, ∑ j, H i j ≤ a) (x : Fin 4 → ℝ) :
    -a * (∑ i, x i ^ 2) ≤ quadraticValue H x := by
  have hr : ∑ i, ∑ j, x i ^ 2 * H i j ≤ a * ∑ i, x i ^ 2 := by
    calc
      _ = ∑ i, x i ^ 2 * (∑ j, H i j) := by simp only [Finset.mul_sum]
      _ ≤ ∑ i, a * x i ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrows i) (sq_nonneg (x i))
      _ = _ := by rw [Finset.mul_sum]
  have hc : ∑ i, ∑ j, x j ^ 2 * H i j ≤ a * ∑ i, x i ^ 2 := by
    rw [Finset.sum_comm]
    simpa only [hsym] using hr
  have hterm (i j : Fin 4) : -(x i ^ 2 * H i j) - x j ^ 2 * H i j ≤ 2 * (x i * H i j * x j) := by
    nlinarith [mul_nonneg (hH i j) (sq_nonneg (x i+x j))]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm i j
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hsum
  have hscale : (∑ i, ∑ j, 2 * (x i * H i j * x j)) =
      2 * (∑ i, ∑ j, x i * H i j * x j) := by simp only [Finset.mul_sum]
  rw [hscale] at hsum
  unfold quadraticValue
  linarith

theorem fourRowComplementCorrection_quadratic_lower {n : ℕ} (T : Board 4 n)
    (hT : ∀ i j, 0 ≤ T i j) (x : Fin 4 → ℝ) :
    -(fourRowColumnSquareMass T / 3) * (∑ i, x i ^ 2) ≤
      quadraticValue (fourRowComplementCorrection T) x :=
  fourRow_symmetric_row_lower _ (fourRowComplementCorrection_nonneg T hT)
    (fourRowComplementCorrection_symmetric T) _ (fourRowComplementCorrection_row_bound T hT) x

theorem fourRowBlendKernel_decomposition {n : ℕ} (T : Board 4 n)
    (hm : totalMass T ≠ 0) (i j : Fin 4) :
    fourRowBlendKernel T i j = (totalMass T ^ 2 / 2) *
      fourRowLeadingKernel (fun r => rowSum T r / totalMass T) i j -
      fourRowColumnSquareMass T / 2 + fourRowComplementCorrection T i j := by
  have hscale := fourRowColumnComplement_scale
    (fun r => rowSum T r / totalMass T) (totalMass T) i j
  have hid : (fun r => totalMass T * (rowSum T r / totalMass T)) = rowSum T := by
    funext r
    field_simp
  rw [hid] at hscale
  have hB : fourRowLeadingKernel (fun r => rowSum T r / totalMass T) i j =
      1 - 2 * fourRowColumnComplement (fun r => rowSum T r / totalMass T) i j := by
    simp only [fourRowLeadingKernel, fourRowColumnComplement]
    split_ifs <;> ring
  rw [fourRowBlendKernel, hB, hscale]
  ring

end DittertRybin
