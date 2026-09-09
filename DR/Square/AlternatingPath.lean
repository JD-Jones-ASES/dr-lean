import DR.Square.IncidenceTransfer
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact Schur bounds for the alternating paths used at square orders five and six. -/

namespace DittertRybin

open scoped BigOperators
open Certificates

private theorem sum_four (f : Fin 4 → ℝ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + f 3)) = _
  ring

private theorem sum_five (f : Fin 5 → ℝ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + f 4))) = _
  ring

private theorem sum_six (f : Fin 6 → ℝ) : (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) = _
  ring

private theorem sum_eleven (f : Fin 11 → ℝ) : (∑ i, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + f 10))))))))) = _
  ring

private theorem sum_twelve (f : Fin 12 → ℝ) : (∑ i, f i) =
    f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10 + f 11 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + (f 7 + (f 8 + (f 9 + (f 10 + f 11)))))))))) = _
  ring

/-- A finite strict Schur estimate, retaining singular and zero-vector subcases explicitly. -/
theorem strict_schur_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (y : ι → ℝ) (z : κ → ℝ) (s : ι → ℝ) (a d c C : ℝ)
    (ha : 0 < a) (hschur : c ^ 2 * C < a * d)
    (hbound : (∑ i, s i ^ 2) ≤ C * ∑ j, z j ^ 2)
    (hnz : 0 < (∑ i, y i ^ 2) + ∑ j, z j ^ 2) :
    0 < a * (∑ i, y i ^ 2) + d * (∑ j, z j ^ 2) - 2 * c * ∑ i, y i * s i := by
  have hY : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hZ : 0 ≤ ∑ j, z j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS : 0 ≤ ∑ i, s i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : 0 ≤ ∑ i, (a * y i - c * s i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have heq (i : ι) : (a * y i - c * s i) ^ 2 =
      a ^ 2 * y i ^ 2 + c ^ 2 * s i ^ 2 - 2 * a * c * (y i * s i) := by ring
  simp_rw [heq, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsq
  by_cases hz0 : (∑ j, z j ^ 2) = 0
  · rw [hz0, mul_zero] at hbound
    have hs0 : (∑ i, s i ^ 2) = 0 := le_antisymm hbound hS
    have hs (i : ι) : s i = 0 := by
      have hle := Finset.single_le_sum (fun i _ => sq_nonneg (s i)) (Finset.mem_univ i)
      nlinarith
    simp only [hs, mul_zero, Finset.sum_const_zero, hz0, add_zero, sub_zero]
    exact mul_pos ha (by linarith)
  · have hzpos : 0 < ∑ j, z j ^ 2 := lt_of_le_of_ne hZ (Ne.symm hz0)
    have hstrict := mul_lt_mul_of_pos_right hschur hzpos
    have hweak := mul_le_mul_of_nonneg_left hbound (sq_nonneg c)
    nlinarith

def joinSix (z : Fin 5 → ℝ) : Fin 6 → ℝ :=
  ![z 0, z 0 + z 1, z 1 + z 2, z 2 + z 3, z 3 + z 4, z 4]

def joinFive (z : Fin 4 → ℝ) : Fin 5 → ℝ :=
  ![z 0, z 0 + z 1, z 1 + z 2, z 2 + z 3, z 3]

def joinShiftSix : Matrix (Fin 5) (Fin 5) ℚ := fun i j =>
  if i = j then 26 / 15 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

def joinShiftFive : Matrix (Fin 4) (Fin 4) ℚ := fun i j =>
  if i = j then 81 / 50 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0

def joinCertificateSix : GramCertificate 5 5 := GramCertificate.ofLDL
  !![1, 0, 0, 0, 0; -15/26, 1, 0, 0, 0; 0, -390/451, 1, 0, 0;
    0, 0, -6765/5876, 1, 0; 0, 0, 0, -88140/51301, 1]
  ![26/15, 451/390, 5876/6765, 51301/88140, 11726/769515]

def joinCertificateFive : GramCertificate 4 4 := GramCertificate.ofLDL
  !![1, 0, 0, 0; -50/81, 1, 0, 0; 0, -4050/4061, 1, 0; 0, 0, -203050/126441, 1]
  ![81/50, 4061/4050, 126441/203050, 89221/6322050]

set_option maxRecDepth 100000 in
theorem joinCertificateSix_valid : joinCertificateSix.Valid joinShiftSix := by decide +kernel

set_option maxRecDepth 100000 in
theorem joinCertificateFive_valid : joinCertificateFive.Valid joinShiftFive := by decide +kernel

theorem joinSix_bound (z : Fin 5 → ℝ) : (∑ i, joinSix z i ^ 2) ≤ (56 / 15) * ∑ j, z j ^ 2 := by
  have h := joinCertificateSix.nonneg joinShiftSix joinCertificateSix_valid z
  norm_num [-Fin.val_eq_zero_iff, quadraticValue, joinShiftSix, Matrix.map_apply, sum_five, Fin.ext_iff] at h
  norm_num [joinSix, sum_six, sum_five]
  dsimp at h ⊢
  nlinarith

theorem joinFive_bound (z : Fin 4 → ℝ) : (∑ i, joinFive z i ^ 2) ≤ (181 / 50) * ∑ j, z j ^ 2 := by
  have h := joinCertificateFive.nonneg joinShiftFive joinCertificateFive_valid z
  norm_num [-Fin.val_eq_zero_iff, quadraticValue, joinShiftFive, Matrix.map_apply, sum_four, Fin.ext_iff] at h
  norm_num [joinFive, sum_five, sum_four]
  dsimp at h ⊢
  nlinarith

noncomputable def weightedPathIncidence {m : ℕ} (w : Fin m → ℝ) :
    Matrix (Fin (m + 1)) (Fin m) ℝ := fun i j =>
  (if i = j.castSucc then Real.sqrt (w j) else 0) -
  (if i = j.succ then Real.sqrt (w j) else 0)

def alternatingWeights (m : ℕ) (q b : ℝ) : Fin m → ℝ :=
  fun j => if j.val % 2 = 0 then q else b

theorem weightedPathIncidence_energy {m : ℕ} (w : Fin m → ℝ) (hw : ∀ j, 0 ≤ w j)
    (f : Fin (m + 1) → ℝ) :
    (∑ j, (∑ i, weightedPathIncidence w i j * f i) ^ 2) =
      ∑ j, w j * sweepGap f j ^ 2 := by
  apply Finset.sum_congr rfl
  intro j _
  have heq : (∑ i, weightedPathIncidence w i j * f i) =
      Real.sqrt (w j) * (f j.castSucc - f j.succ) := by
    simp [weightedPathIncidence, sub_mul, Finset.sum_sub_distrib, mul_sub]
  rw [heq, mul_pow, Real.sq_sqrt (hw j)]
  unfold sweepGap
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem alternating_twelve_gram_identity (q b : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b)
    (v : Fin 11 → ℝ) :
    (∑ i, (∑ j, weightedPathIncidence (alternatingWeights 11 q b) i j * v j) ^ 2) =
      2 * q * (∑ i, (![v 0, v 2, v 4, v 6, v 8, v 10] : Fin 6 → ℝ) i ^ 2) +
      2 * b * (∑ j, (![v 1, v 3, v 5, v 7, v 9] : Fin 5 → ℝ) j ^ 2) -
      2 * (Real.sqrt q * Real.sqrt b) *
        (∑ i, (![v 0, v 2, v 4, v 6, v 8, v 10] : Fin 6 → ℝ) i *
          joinSix ![v 1, v 3, v 5, v 7, v 9] i) := by
  rw [sum_twelve]
  norm_num [-Fin.val_eq_zero_iff, weightedPathIncidence, alternatingWeights, joinSix, sum_twelve, sum_eleven,
    sum_six, sum_five, Fin.ext_iff]
  dsimp
  ring_nf
  simp [Real.sq_sqrt hq, Real.sq_sqrt hb]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem alternating_twelve_range (q b : ℝ) (hq : 0 < q) (hb : 0 < b)
    (f : Fin 12 → ℝ) (hf : ∑ i, f i = 0) :
    ∃ v : Fin 11 → ℝ, ∀ i,
      f i = ∑ j, weightedPathIncidence (alternatingWeights 11 q b) i j * v j := by
  refine ⟨![(f 0) / Real.sqrt q,
    (f 0 + f 1) / Real.sqrt b,
    (f 0 + f 1 + f 2) / Real.sqrt q,
    (f 0 + f 1 + f 2 + f 3) / Real.sqrt b,
    (f 0 + f 1 + f 2 + f 3 + f 4) / Real.sqrt q,
    (f 0 + f 1 + f 2 + f 3 + f 4 + f 5) / Real.sqrt b,
    (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6) / Real.sqrt q,
    (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7) / Real.sqrt b,
    (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8) / Real.sqrt q,
    (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9) / Real.sqrt b,
    (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9 + f 10) / Real.sqrt q], ?_⟩
  have hq0 := (Real.sqrt_pos.mpr hq).ne'
  have hb0 := (Real.sqrt_pos.mpr hb).ne'
  rw [sum_twelve] at hf
  intro i
  fin_cases i <;>
    norm_num [-Fin.val_eq_zero_iff, weightedPathIncidence, alternatingWeights, sum_eleven, Fin.ext_iff,
      mul_div_cancel₀, hq0, hb0] <;> dsimp <;>
      field_simp [hq0, hb0] <;> nlinarith

/-- The rational inversion threshold; its denominator is always proved positive where used. -/
noncomputable def alternatingBoundary (q h κ : ℝ) : ℝ :=
  h * (2 * q - h) / (2 * (q * κ - h))

theorem alternating_twelve_gram_strict (q b h : ℝ) (hq : 0 < q) (hh : 0 ≤ h)
    (hhq : h < q * (2 / 15)) (hb : alternatingBoundary q h (2 / 15) < b)
    (v : Fin 11 → ℝ) (hv : v ≠ 0) :
    h * (∑ j, v j ^ 2) <
      ∑ i, (∑ j, weightedPathIncidence (alternatingWeights 11 q b) i j * v j) ^ 2 := by
  have hden : 0 < 2 * (q * (2 / 15) - h) := by linarith
  have hq2 : 0 < 2 * q - h := by linarith
  have hB0 : 0 ≤ alternatingBoundary q h (2 / 15) :=
    div_nonneg (mul_nonneg hh hq2.le) hden.le
  have hb0 : 0 < b := lt_of_le_of_lt hB0 hb
  have hmul := (div_lt_iff₀ hden).mp hb
  have hcsq : (Real.sqrt q * Real.sqrt b) ^ 2 = q * b := by
    rw [mul_pow, Real.sq_sqrt hq.le, Real.sq_sqrt hb0.le]
  have hschur : (Real.sqrt q * Real.sqrt b) ^ 2 * (56 / 15) < (2 * q - h) * (2 * b - h) := by
    rw [hcsq]
    nlinarith
  have hvpos : 0 < ∑ j, v j ^ 2 := by
    have hex : ∃ j, v j ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hv (funext hn)
    obtain ⟨j, hj⟩ := hex
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hj)
      (Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j))
  have hsplit : (∑ j, v j ^ 2) =
      (∑ i, (![v 0, v 2, v 4, v 6, v 8, v 10] : Fin 6 → ℝ) i ^ 2) +
      ∑ j, (![v 1, v 3, v 5, v 7, v 9] : Fin 5 → ℝ) j ^ 2 := by
    norm_num [sum_eleven, sum_six, sum_five]; dsimp; ring
  have hstrict := strict_schur_sum ![v 0, v 2, v 4, v 6, v 8, v 10]
    ![v 1, v 3, v 5, v 7, v 9] (joinSix ![v 1, v 3, v 5, v 7, v 9])
    (2 * q - h) (2 * b - h) (Real.sqrt q * Real.sqrt b) (56 / 15)
    hq2 hschur (joinSix_bound _) (by rwa [← hsplit])
  rw [alternating_twelve_gram_identity q b hq.le hb0.le, hsplit]
  nlinarith

/-- Strict coercivity at any h below the inversion threshold, proved through finite Gram algebra. -/
theorem alternating_twelve_strict (q b h : ℝ) (hq : 0 < q) (hh : 0 ≤ h)
    (hhq : h < q * (2 / 15)) (hb : alternatingBoundary q h (2 / 15) < b)
    (f : Fin 12 → ℝ) (hf : ∑ i, f i = 0) (hf0 : 0 < ∑ i, f i ^ 2) :
    h * (∑ i, f i ^ 2) < ∑ j, alternatingWeights 11 q b j * sweepGap f j ^ 2 := by
  have hden : 0 < 2 * (q * (2 / 15) - h) := by linarith
  have hq2 : 0 < 2 * q - h := by linarith
  have hB0 : 0 ≤ alternatingBoundary q h (2 / 15) :=
    div_nonneg (mul_nonneg hh hq2.le) hden.le
  have hb0 : 0 < b := lt_of_le_of_lt hB0 hb
  have hw (j : Fin 11) : 0 ≤ alternatingWeights 11 q b j := by
    unfold alternatingWeights; split <;> positivity
  have h := incidence_strict_bound_transfer (weightedPathIncidence (alternatingWeights 11 q b)) h
    (alternating_twelve_gram_strict q b h hq hh hhq hb) f hf0 (alternating_twelve_range q b hq hb0 f hf)
  rwa [weightedPathIncidence_energy _ hw] at h

end DittertRybin
