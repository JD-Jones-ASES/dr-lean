import DR.Certificates.FiniteK3Soundness
import Mathlib.Algebra.Order.Star.Real

namespace DittertRybin.Certificates
open scoped BigOperators

-- PSD alone permits an additional kernel and cannot force uniform equality.
example : (∑ a : Fin 2, ∑ b : Fin 2, unorderedPairWeight a b *
    (![1,0] : Fin 2 → ℝ) a * (![1,0] : Fin 2 → ℝ) b *
      quadraticValue (0 : Matrix (Fin 2) (Fin 2) ℝ) ![1,0]) = 0 := by
  simp [quadraticValue]
example : ¬∃ t : ℝ, ∀ a : Fin 2, (![1,0] : Fin 2 → ℝ) a = t := by
  rintro ⟨t,ht⟩
  have h0 := ht 0
  have h1 := ht 1
  norm_num at h0 h1
  linarith

-- Mass-one gives at least one positive diagonal even on a support face.
example : (∑ a : Fin 3, (![0,1,0] : Fin 3 → ℝ) a)=1 ∧
    unorderedPairWeight (1 : Fin 3) 1 * (1:ℝ)^2 = 1 := by
  norm_num [Fin.sum_univ_succ,unorderedPairWeight]

-- Dropping nonnegative cell weights makes a PSD certificate sum negative.
private def diagonalOnly (a b : Fin 2) : Matrix (Fin 2) (Fin 2) ℝ :=
  if a=b then 0 else 1
example (a b : Fin 2) : (diagonalOnly a b).PosSemidef := by
  unfold diagonalOnly
  split_ifs
  · exact Matrix.PosSemidef.zero
  · exact Matrix.PosSemidef.one
example : (∑ a : Fin 2,∑ b : Fin 2,unorderedPairWeight a b *
    (![2,-1] : Fin 2 → ℝ) a * (![2,-1] : Fin 2 → ℝ) b *
      quadraticValue (diagonalOnly a b) ![2,-1]) = -10 := by
  norm_num [Fin.sum_univ_succ,unorderedPairWeight,quadraticValue,diagonalOnly,Matrix.one_apply]

#print axioms weightedPair_zero_forces_constant
#print axioms finiteK3_uniformMaximizer

end DittertRybin.Certificates
