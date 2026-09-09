import DR.Rectangular.FourRowFiniteData5Block1
import Mathlib.Tactic.FinCases

namespace DittertRybin
open Certificates

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block1Gram_valid_0 :
    (fourRowFinite5Block1Gram 0).StrictValid (fourRowFinite5Block1Bernstein 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block1Gram_valid_1 :
    (fourRowFinite5Block1Gram 1).StrictValid (fourRowFinite5Block1Bernstein 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block1Gram_valid_2 :
    (fourRowFinite5Block1Gram 2).StrictValid (fourRowFinite5Block1Bernstein 2) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block1Gram_valid_3 :
    (fourRowFinite5Block1Gram 3).StrictValid (fourRowFinite5Block1Bernstein 3) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block1Gram_valid_4 :
    (fourRowFinite5Block1Gram 4).StrictValid (fourRowFinite5Block1Bernstein 4) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block1Gram_valid_5 :
    (fourRowFinite5Block1Gram 5).StrictValid (fourRowFinite5Block1Bernstein 5) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block1Gram_valid_6 :
    (fourRowFinite5Block1Gram 6).StrictValid (fourRowFinite5Block1Bernstein 6) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block1Gram_valid_7 :
    (fourRowFinite5Block1Gram 7).StrictValid (fourRowFinite5Block1Bernstein 7) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block1Gram_valid_8 :
    (fourRowFinite5Block1Gram 8).StrictValid (fourRowFinite5Block1Bernstein 8) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite5Block1Gram_valid_9 :
    (fourRowFinite5Block1Gram 9).StrictValid (fourRowFinite5Block1Bernstein 9) := by
  decide +kernel

theorem fourRowFinite5Block1Gram_valid (k : Fin 10) :
    (fourRowFinite5Block1Gram k).StrictValid (fourRowFinite5Block1Bernstein k) := by
  fin_cases k
  · exact fourRowFinite5Block1Gram_valid_0
  · exact fourRowFinite5Block1Gram_valid_1
  · exact fourRowFinite5Block1Gram_valid_2
  · exact fourRowFinite5Block1Gram_valid_3
  · exact fourRowFinite5Block1Gram_valid_4
  · exact fourRowFinite5Block1Gram_valid_5
  · exact fourRowFinite5Block1Gram_valid_6
  · exact fourRowFinite5Block1Gram_valid_7
  · exact fourRowFinite5Block1Gram_valid_8
  · exact fourRowFinite5Block1Gram_valid_9

theorem fourRowFinite5Block1Bernstein_posDef (k : Fin 10) :
    ((fourRowFinite5Block1Bernstein k).map (fun q : ℚ => (q : ℝ))).PosDef :=
  (fourRowFinite5Block1Gram k).strictValid_posDef _ (fourRowFinite5Block1Gram_valid k)

end DittertRybin
