import DR.Rectangular.FourRowFiniteData50Block14
import Mathlib.Tactic.FinCases

namespace DittertRybin
open Certificates

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block14Gram_valid_0 :
    (fourRowFinite50Block14Gram 0).StrictValid (fourRowFinite50Block14Bernstein 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block14Gram_valid_1 :
    (fourRowFinite50Block14Gram 1).StrictValid (fourRowFinite50Block14Bernstein 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block14Gram_valid_2 :
    (fourRowFinite50Block14Gram 2).StrictValid (fourRowFinite50Block14Bernstein 2) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block14Gram_valid_3 :
    (fourRowFinite50Block14Gram 3).StrictValid (fourRowFinite50Block14Bernstein 3) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block14Gram_valid_4 :
    (fourRowFinite50Block14Gram 4).StrictValid (fourRowFinite50Block14Bernstein 4) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block14Gram_valid_5 :
    (fourRowFinite50Block14Gram 5).StrictValid (fourRowFinite50Block14Bernstein 5) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block14Gram_valid_6 :
    (fourRowFinite50Block14Gram 6).StrictValid (fourRowFinite50Block14Bernstein 6) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block14Gram_valid_7 :
    (fourRowFinite50Block14Gram 7).StrictValid (fourRowFinite50Block14Bernstein 7) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block14Gram_valid_8 :
    (fourRowFinite50Block14Gram 8).StrictValid (fourRowFinite50Block14Bernstein 8) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block14Gram_valid_9 :
    (fourRowFinite50Block14Gram 9).StrictValid (fourRowFinite50Block14Bernstein 9) := by
  decide +kernel

theorem fourRowFinite50Block14Gram_valid (k : Fin 10) :
    (fourRowFinite50Block14Gram k).StrictValid (fourRowFinite50Block14Bernstein k) := by
  fin_cases k
  · exact fourRowFinite50Block14Gram_valid_0
  · exact fourRowFinite50Block14Gram_valid_1
  · exact fourRowFinite50Block14Gram_valid_2
  · exact fourRowFinite50Block14Gram_valid_3
  · exact fourRowFinite50Block14Gram_valid_4
  · exact fourRowFinite50Block14Gram_valid_5
  · exact fourRowFinite50Block14Gram_valid_6
  · exact fourRowFinite50Block14Gram_valid_7
  · exact fourRowFinite50Block14Gram_valid_8
  · exact fourRowFinite50Block14Gram_valid_9

theorem fourRowFinite50Block14Bernstein_posDef (k : Fin 10) :
    ((fourRowFinite50Block14Bernstein k).map (fun q : ℚ => (q : ℝ))).PosDef :=
  (fourRowFinite50Block14Gram k).strictValid_posDef _ (fourRowFinite50Block14Gram_valid k)

end DittertRybin
