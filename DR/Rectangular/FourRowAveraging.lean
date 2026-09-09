import DR.Rectangular.FourRowRook
import DR.Rectangular.FourRowBlendBounds

/-!
# The analytic four-row floor for actual iid column averaging

The kernel is now identified with the true rook coefficient. The exact blend
identity and its strict gain therefore concern the original sampling functional.
The remaining-column concentration hypotheses remain explicit prerequisites.
-/

namespace DittertRybin

open scoped BigOperators
open Certificates

/-- The factor 24 is the ordering count for the four actual iid samples. -/
theorem fourRow_separationProbability_blend_identity {n : ℕ} (P : Board 4 n)
    (a b : Fin n) (hab : a ≠ b) (s : ℝ) :
    separationProbability (blendColumns P a b s) 4 - separationProbability P 4 =
      24 * (s * (1 - s)) * quadraticValue
        (fourRowBlendKernel (eraseColumns P {a,b})) (fun i => P i a - P i b) := by
  have h := separationProbability_blend_identity (k := 2) P a b hab s
  rw [← fourRowBlendKernel_eq_averagingKernel] at h
  norm_num [Nat.factorial] at h
  rw [h]
  unfold quadraticValue
  ring

/-- Quantitative gain for the actual semimatching functional, including boundary columns. -/
theorem fourRow_separationProbability_blend_gain {n : ℕ} (P : Board 4 n)
    (hP : ∀ i j, 0 ≤ P i j) (a b : Fin n) (hab : a ≠ b) (s : ℝ)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hm : 493 / 500 ≤ totalMass (eraseColumns P {a,b}))
    (hα : fourRowColumnSquareMass (eraseColumns P {a,b}) ≤ 7 / 2500)
    (hν : fourRowMarginalVariance (fun i => rowSum (eraseColumns P {a,b}) i /
      totalMass (eraseColumns P {a,b})) ≤ 1 / 40) :
    24 * (s * (1 - s)) * (13965659 / 8688000000) *
        (∑ i, (P i a - P i b) ^ 2) ≤
      separationProbability (blendColumns P a b s) 4 - separationProbability P 4 := by
  have hT : ∀ i j, 0 ≤ eraseColumns P {a,b} i j := by
    intro i j
    unfold eraseColumns
    split_ifs
    · exact le_rfl
    · exact hP i j
  have hf := fourRowBlendKernel_uniform_floor (eraseColumns P {a,b}) hT hm hα hν
    (fun i => P i a - P i b)
  have hfac : 0 ≤ 24 * (s * (1 - s)) := by positivity
  rw [fourRow_separationProbability_blend_identity P a b hab]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hf hfac

/-- Distinct columns strictly improve under any interior blend in the certified region. -/
theorem fourRow_separationProbability_blend_strict {n : ℕ} (P : Board 4 n)
    (hP : ∀ i j, 0 ≤ P i j) (a b : Fin n) (hab : a ≠ b) (s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hdiff : ∃ i, P i a ≠ P i b)
    (hm : 493 / 500 ≤ totalMass (eraseColumns P {a,b}))
    (hα : fourRowColumnSquareMass (eraseColumns P {a,b}) ≤ 7 / 2500)
    (hν : fourRowMarginalVariance (fun i => rowSum (eraseColumns P {a,b}) i /
      totalMass (eraseColumns P {a,b})) ≤ 1 / 40) :
    separationProbability P 4 < separationProbability (blendColumns P a b s) 4 := by
  have hE : 0 < ∑ i, (P i a - P i b) ^ 2 := by
    apply (Finset.sum_pos_iff_of_nonneg (fun i _ => sq_nonneg (P i a - P i b))).mpr
    obtain ⟨i, hi⟩ := hdiff
    exact ⟨i, Finset.mem_univ _, sq_pos_of_ne_zero (sub_ne_zero.mpr hi)⟩
  have hgain := fourRow_separationProbability_blend_gain P hP a b hab s hs.le hs1.le hm hα hν
  have hpos : 0 < 24 * (s * (1 - s)) * (13965659 / 8688000000) *
      (∑ i, (P i a - P i b) ^ 2) := by positivity
  linarith

/-- At a full-simplex global maximum, the certified pair of columns must coincide. -/
theorem fourRow_columns_eq_of_globalMax {n : ℕ} (P : Board 4 n) (hP : IsProbability P)
    (hmax : ∀ Q : Board 4 n, IsProbability Q → separationProbability Q 4 ≤
      separationProbability P 4) (a b : Fin n)
    (hm : 493 / 500 ≤ totalMass (eraseColumns P {a,b}))
    (hα : fourRowColumnSquareMass (eraseColumns P {a,b}) ≤ 7 / 2500)
    (hν : fourRowMarginalVariance (fun i => rowSum (eraseColumns P {a,b}) i /
      totalMass (eraseColumns P {a,b})) ≤ 1 / 40) :
    ∀ i, P i a = P i b := by
  by_cases hab : a = b
  · simp [hab]
  intro i
  by_contra hi
  have hstrict := fourRow_separationProbability_blend_strict P hP.1 a b hab (1/2)
    (by norm_num) (by norm_num) ⟨i, hi⟩ hm hα hν
  have hle := hmax (blendColumns P a b (1/2))
    (blendColumns_isProbability hP a b hab (1/2) (by norm_num) (by norm_num))
  exact (not_lt_of_ge hle) hstrict

end DittertRybin
