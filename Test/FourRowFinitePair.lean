import DR.Rectangular.FourRowFinitePairSoundness
import DR.Rectangular.FourRowFiniteFastKernel

namespace DittertRybin.Tests
open Certificates
noncomputable section

-- Pair representatives retain the chosen ordinary labels when the endpoints swap.
example : fourRowFinitePairLabels ((OrdinaryPair.different : OrdinaryPair (Fin 3)).swap) =
    (3,4) := rfl

example : fourRowFinitePairLabels ((OrdinaryPair.different : OrdinaryPair (Fin 3)).swap) ≠
    (4,3) := by decide

example (h : ℕ → ℝ) : TwoAxisOrdinarySymm (fourRowFiniteSeedRelationKernel 9 h) :=
  fourRowFiniteSeedRelationKernel_symm 9 h

-- Count one removes the different-ordinary contribution even if it is negative.
example : ordinaryPairAverage 1
    (fun p : OrdinaryPair (Fin 0) => if p = .same then 2 else -7)
    (.inr ()) (.inr ()) = 2 := by norm_num

example : fourRowFiniteOrdinaryAverage 0 2
    (fun i j => if i = j then 2 else -7) 0 0 = -5/2 := by
  norm_num [fourRowFiniteOrdinaryAverage]

-- The last lexicographic coordinate is the omitted ordinary/ordinary coordinate.
example : fourRowFiniteSeedCompressedEquiv 9 (.inr (),.inr ()) = (15 : Fin 16) := by
  rfl

example : fourRowFiniteSeedWeight 9 5
    (fourRowFiniteSeedCompressedEquiv 9 (.inr (),.inr ())).val = 2 := by
  rw [fourRowFiniteSeedWeight_reindex]
  change ((4 : ℝ)-3)*(5-3) = 2
  norm_num

example (N : ℝ) (p : (Fin 3 ⊕ Unit) × (Fin 3 ⊕ Unit)) :
    fourRowFiniteSeedWeight 9 N (fourRowFiniteSeedCompressedEquiv 9 p).val =
      twoAxisAggregateWeight 1 (N-3) p := by
  simpa only [fourRowFiniteSeedRows,fourRowFiniteSeedColumns,Matrix.cons_val,
    Nat.cast_ofNat,show (4 : ℝ)-3 = 1 by norm_num] using
      fourRowFiniteSeedWeight_reindex 9 N p

-- The fast evaluator is an equality of the actual coefficients, for arbitrary signed data.
example (h : Fin 391 → Fin 5 → ℚ) (a : ℕ) (s : Fin 10)
    (i : Fin (fourRowFiniteSeedFullSize s)) :
    fourRowFiniteSeedKernelPowerFast h a s i = fourRowFiniteSeedKernelPower h a s i :=
  fourRowFiniteSeedKernelPowerFast_eq h a s i

#print axioms fourRowFiniteSeedPairKey_swap
#print axioms fourRowFinitePairAverage_eq
#print axioms fourRowFiniteSeedFullMatrix_reindex
#print axioms fourRowFiniteSeedWeight_reindex
#print axioms fourRowFiniteSeedFullMatrix_criterion
#print axioms fourRowFiniteSeedRelation_criterion
#print axioms fourRowFiniteSeedKernelPowerFast_eq

end
end DittertRybin.Tests
