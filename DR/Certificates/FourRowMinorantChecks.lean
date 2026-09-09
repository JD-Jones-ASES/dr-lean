import DR.Certificates.FourRowMinorantCheck00
import DR.Certificates.FourRowMinorantCheck01
import DR.Certificates.FourRowMinorantCheck02
import DR.Certificates.FourRowMinorantCheck03
import DR.Certificates.FourRowMinorantCheck04
import DR.Certificates.FourRowMinorantCheck05
import DR.Certificates.FourRowMinorantCheck06
import DR.Certificates.FourRowMinorantCheck07
import DR.Certificates.FourRowMinorantCheck08
import DR.Certificates.FourRowMinorantCheck09
import DR.Certificates.FourRowMinorantCheck10
import DR.Certificates.FourRowMinorantCheck11
import DR.Certificates.FourRowMinorantCheck12
import DR.Certificates.FourRowMinorantCheck13
import DR.Certificates.FourRowMinorantCheck14
import DR.Certificates.FourRowMinorantCheck15
import DR.Certificates.FourRowMinorantCheck16
import DR.Certificates.FourRowMinorantCheck17
import DR.Certificates.FourRowMinorantCheck18
import DR.Certificates.FourRowMinorantCheck19
import DR.Certificates.FourRowMinorantCheck20
import DR.Certificates.FourRowMinorantCheck21
import DR.Certificates.FourRowMinorantCheck22
import DR.Certificates.FourRowMinorantCheck23
import DR.Certificates.FourRowMinorantCheck24
import DR.Certificates.FourRowMinorantCheck25
import DR.Certificates.FourRowMinorantCheck26
import DR.Certificates.FourRowMinorantCheck27
import DR.Certificates.FourRowMinorantCheck28
import DR.Certificates.FourRowMinorantCheck29
import DR.Certificates.FourRowMinorantCheck30
import DR.Certificates.FourRowMinorantCheck31
import DR.Certificates.FourRowMinorantCheck32
import DR.Certificates.FourRowMinorantCheck33
import DR.Certificates.FourRowMinorantCheck34

/-! Complete coefficient coverage, with the source's exact positive margin. -/
namespace DittertRybin.Certificates.FourRowMinorant
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem compactBernsteinNumerator_nonneg (i j k : Fin 35) :
    0 ≤ compactBernsteinNumerator i j k := by
  fin_cases i
  · exact compactBernsteinNumerator_row_0 j k
  · exact compactBernsteinNumerator_row_1 j k
  · exact compactBernsteinNumerator_row_2 j k
  · exact compactBernsteinNumerator_row_3 j k
  · exact compactBernsteinNumerator_row_4 j k
  · exact compactBernsteinNumerator_row_5 j k
  · exact compactBernsteinNumerator_row_6 j k
  · exact compactBernsteinNumerator_row_7 j k
  · exact compactBernsteinNumerator_row_8 j k
  · exact compactBernsteinNumerator_row_9 j k
  · exact compactBernsteinNumerator_row_10 j k
  · exact compactBernsteinNumerator_row_11 j k
  · exact compactBernsteinNumerator_row_12 j k
  · exact compactBernsteinNumerator_row_13 j k
  · exact compactBernsteinNumerator_row_14 j k
  · exact compactBernsteinNumerator_row_15 j k
  · exact compactBernsteinNumerator_row_16 j k
  · exact compactBernsteinNumerator_row_17 j k
  · exact compactBernsteinNumerator_row_18 j k
  · exact compactBernsteinNumerator_row_19 j k
  · exact compactBernsteinNumerator_row_20 j k
  · exact compactBernsteinNumerator_row_21 j k
  · exact compactBernsteinNumerator_row_22 j k
  · exact compactBernsteinNumerator_row_23 j k
  · exact compactBernsteinNumerator_row_24 j k
  · exact compactBernsteinNumerator_row_25 j k
  · exact compactBernsteinNumerator_row_26 j k
  · exact compactBernsteinNumerator_row_27 j k
  · exact compactBernsteinNumerator_row_28 j k
  · exact compactBernsteinNumerator_row_29 j k
  · exact compactBernsteinNumerator_row_30 j k
  · exact compactBernsteinNumerator_row_31 j k
  · exact compactBernsteinNumerator_row_32 j k
  · exact compactBernsteinNumerator_row_33 j k
  · exact compactBernsteinNumerator_row_34 j k

theorem compactBernsteinNumerator_margin (i j k : Fin 35) :
    (i=0 ∧ j=0 ∧ k=0) ∨ 6323724 ≤ compactBernsteinNumerator i j k := by
  fin_cases i
  · exact compactBernsteinNumerator_margin_row_0 j k
  · exact compactBernsteinNumerator_margin_row_1 j k
  · exact compactBernsteinNumerator_margin_row_2 j k
  · exact compactBernsteinNumerator_margin_row_3 j k
  · exact compactBernsteinNumerator_margin_row_4 j k
  · exact compactBernsteinNumerator_margin_row_5 j k
  · exact compactBernsteinNumerator_margin_row_6 j k
  · exact compactBernsteinNumerator_margin_row_7 j k
  · exact compactBernsteinNumerator_margin_row_8 j k
  · exact compactBernsteinNumerator_margin_row_9 j k
  · exact compactBernsteinNumerator_margin_row_10 j k
  · exact compactBernsteinNumerator_margin_row_11 j k
  · exact compactBernsteinNumerator_margin_row_12 j k
  · exact compactBernsteinNumerator_margin_row_13 j k
  · exact compactBernsteinNumerator_margin_row_14 j k
  · exact compactBernsteinNumerator_margin_row_15 j k
  · exact compactBernsteinNumerator_margin_row_16 j k
  · exact compactBernsteinNumerator_margin_row_17 j k
  · exact compactBernsteinNumerator_margin_row_18 j k
  · exact compactBernsteinNumerator_margin_row_19 j k
  · exact compactBernsteinNumerator_margin_row_20 j k
  · exact compactBernsteinNumerator_margin_row_21 j k
  · exact compactBernsteinNumerator_margin_row_22 j k
  · exact compactBernsteinNumerator_margin_row_23 j k
  · exact compactBernsteinNumerator_margin_row_24 j k
  · exact compactBernsteinNumerator_margin_row_25 j k
  · exact compactBernsteinNumerator_margin_row_26 j k
  · exact compactBernsteinNumerator_margin_row_27 j k
  · exact compactBernsteinNumerator_margin_row_28 j k
  · exact compactBernsteinNumerator_margin_row_29 j k
  · exact compactBernsteinNumerator_margin_row_30 j k
  · exact compactBernsteinNumerator_margin_row_31 j k
  · exact compactBernsteinNumerator_margin_row_32 j k
  · exact compactBernsteinNumerator_margin_row_33 j k
  · exact compactBernsteinNumerator_margin_row_34 j k

theorem compactBernsteinNumerator_zero : compactBernsteinNumerator 0 0 0 = 0 := by decide +kernel

theorem coefficient_count : Fintype.card (Fin 35 × Fin 35 × Fin 35) = 42875 := by norm_num

end DittertRybin.Certificates.FourRowMinorant
