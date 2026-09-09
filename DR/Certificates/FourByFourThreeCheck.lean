import DR.Certificates.FourByFourThreeDefinitions
import Mathlib.Data.Fintype.Pi

namespace DittertRybin.Certificates
open scoped BigOperators

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem fourByFourThreeGram_valid :
    fourByFourThreeGram.Valid (fourByFourThreeShift.submatrix Fin.castSucc Fin.castSucc) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem fourByFourThreeMatrix_checks :
    (∀ i j,fourByFourThreeShift i j=fourByFourThreeShift j i) ∧
    (∀ i,(∑ j,fourByFourThreeShift i j)=0) ∧
    (∀ i,(∑ j,fourByFourThreeSeed i j)=0) := by
  unfold fourByFourThreeShift fourByFourThreeSeed centeringMatrix Matrix
  decide +kernel

/-- The literal distinct-row OR distinct-column predicate on three physical cells. -/
def fourByFourThreeSuccess (a b c : Fin 16) : Prop :=
  (a.val/4≠b.val/4 ∧ a.val/4≠c.val/4 ∧ b.val/4≠c.val/4) ∨
  (a.val%4≠b.val%4 ∧ a.val%4≠c.val%4 ∧ b.val%4≠c.val%4)

instance (a b c : Fin 16) : Decidable (fourByFourThreeSuccess a b c) := by
  unfold fourByFourThreeSuccess
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
/-- A finite structural gate for the homogeneous cubic identity. No weights are sampled. -/
theorem fourByFourThree_triple_identity : ∀ a b c : Fin 16,
    fourByFourThreeMatrix a b c+fourByFourThreeMatrix b a c+fourByFourThreeMatrix c a b=
      3*((39/64:ℚ)-if fourByFourThreeSuccess a b c then 1 else 0) := by
  decide +kernel

end DittertRybin.Certificates
