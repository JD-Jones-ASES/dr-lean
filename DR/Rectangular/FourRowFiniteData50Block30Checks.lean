import DR.Rectangular.FourRowFiniteData50Block30
import Mathlib.Tactic.FinCases

namespace DittertRybin
open Certificates

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block30Gram_valid_0 :
    (fourRowFinite50Block30Gram 0).StrictValid (fourRowFinite50Block30Bernstein 0) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block30Gram_valid_1 :
    (fourRowFinite50Block30Gram 1).StrictValid (fourRowFinite50Block30Bernstein 1) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block30Gram_valid_2 :
    (fourRowFinite50Block30Gram 2).StrictValid (fourRowFinite50Block30Bernstein 2) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block30Gram_valid_3 :
    (fourRowFinite50Block30Gram 3).StrictValid (fourRowFinite50Block30Bernstein 3) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block30Gram_valid_4 :
    (fourRowFinite50Block30Gram 4).StrictValid (fourRowFinite50Block30Bernstein 4) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block30Gram_valid_5 :
    (fourRowFinite50Block30Gram 5).StrictValid (fourRowFinite50Block30Bernstein 5) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block30Gram_valid_6 :
    (fourRowFinite50Block30Gram 6).StrictValid (fourRowFinite50Block30Bernstein 6) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block30Gram_valid_7 :
    (fourRowFinite50Block30Gram 7).StrictValid (fourRowFinite50Block30Bernstein 7) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block30Gram_valid_8 :
    (fourRowFinite50Block30Gram 8).StrictValid (fourRowFinite50Block30Bernstein 8) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem fourRowFinite50Block30Gram_valid_9 :
    (fourRowFinite50Block30Gram 9).StrictValid (fourRowFinite50Block30Bernstein 9) := by
  decide +kernel

theorem fourRowFinite50Block30Gram_valid (k : Fin 10) :
    (fourRowFinite50Block30Gram k).StrictValid (fourRowFinite50Block30Bernstein k) := by
  fin_cases k
  · exact fourRowFinite50Block30Gram_valid_0
  · exact fourRowFinite50Block30Gram_valid_1
  · exact fourRowFinite50Block30Gram_valid_2
  · exact fourRowFinite50Block30Gram_valid_3
  · exact fourRowFinite50Block30Gram_valid_4
  · exact fourRowFinite50Block30Gram_valid_5
  · exact fourRowFinite50Block30Gram_valid_6
  · exact fourRowFinite50Block30Gram_valid_7
  · exact fourRowFinite50Block30Gram_valid_8
  · exact fourRowFinite50Block30Gram_valid_9

theorem fourRowFinite50Block30Bernstein_posDef (k : Fin 10) :
    ((fourRowFinite50Block30Bernstein k).map (fun q : ℚ => (q : ℝ))).PosDef :=
  (fourRowFinite50Block30Gram k).strictValid_posDef _ (fourRowFinite50Block30Gram_valid k)

end DittertRybin
