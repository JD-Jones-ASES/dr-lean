import DR.Certificates.FourByFiveThreeEntries
import Mathlib.Tactic.FinCases

namespace DittertRybin.Certificates
open scoped BigOperators

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourByFiveThreeGram_valid_0 :
    (fourByFiveThreeGram 0).Valid ((fourByFiveThreeTableShift 0).submatrix Fin.castSucc Fin.castSucc) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourByFiveThreeGram_valid_1 :
    (fourByFiveThreeGram 1).Valid ((fourByFiveThreeTableShift 1).submatrix Fin.castSucc Fin.castSucc) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourByFiveThreeGram_valid_2 :
    (fourByFiveThreeGram 2).Valid ((fourByFiveThreeTableShift 2).submatrix Fin.castSucc Fin.castSucc) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourByFiveThreeGram_valid_3 :
    (fourByFiveThreeGram 3).Valid ((fourByFiveThreeTableShift 3).submatrix Fin.castSucc Fin.castSucc) := by
  decide +kernel

theorem fourByFiveThreeGram_valid (s : Fin 4) :
    (fourByFiveThreeGram s).Valid ((fourByFiveThreeShift s).submatrix Fin.castSucc Fin.castSucc) := by
  rw [fourByFiveThreeShift_eq_table]
  fin_cases s
  · exact fourByFiveThreeGram_valid_0
  · exact fourByFiveThreeGram_valid_1
  · exact fourByFiveThreeGram_valid_2
  · exact fourByFiveThreeGram_valid_3

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem fourByFiveThreeMatrix_checks : ∀ s : Fin 4,
    (∀ i j,fourByFiveThreeShift s i j=fourByFiveThreeShift s j i) ∧
    (∀ i,(∑ j,fourByFiveThreeShift s i j)=0) ∧
    (∀ i,(∑ j,fourByFiveThreeSeed s i j)=0) := by
  simp_rw [fourByFiveThreeShift_eq_table, fourByFiveThreeSeed_eq_table]
  unfold fourByFiveThreeTableShift fourByFiveThreeTableMatrix centeringMatrix Matrix
  decide +kernel

end DittertRybin.Certificates
