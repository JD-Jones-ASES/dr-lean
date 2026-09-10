import DR.Certificates.FiniteK3Dispatch.M4N6To21
import DR.Certificates.FiniteK3Dispatch.M4N22To37
import DR.Certificates.FiniteK3Dispatch.M4N38To53
import DR.Certificates.FiniteK3Dispatch.M4N54To69
import DR.Certificates.FiniteK3Dispatch.M4N70To85
import DR.Certificates.FiniteK3Dispatch.M4N86To101
import DR.Certificates.FiniteK3Dispatch.M4N102To117
import DR.Certificates.FiniteK3Dispatch.M4N118To133
import DR.Certificates.FiniteK3Dispatch.M4N134To149
import DR.Certificates.FiniteK3Dispatch.M4N150To165
import DR.Certificates.FiniteK3Dispatch.M4N166To181
import DR.Certificates.FiniteK3Dispatch.M4N182To197
import DR.Certificates.FiniteK3Dispatch.M4N198To213
import DR.Certificates.FiniteK3Dispatch.M4N214To229
import DR.Certificates.FiniteK3Dispatch.M4N230To245
import DR.Certificates.FiniteK3Dispatch.M4N246To261
import DR.Certificates.FiniteK3Dispatch.M4N262To277
import DR.Certificates.FiniteK3Dispatch.M4N278To293
import DR.Certificates.FiniteK3Dispatch.M4N294To309
import DR.Certificates.FiniteK3Dispatch.M4N310To325
import DR.Certificates.FiniteK3Dispatch.M4N326To341
import DR.Certificates.FiniteK3Dispatch.M4N342To357
import DR.Certificates.FiniteK3Dispatch.M4N358To373
import DR.Certificates.FiniteK3Dispatch.M4N374To389
import DR.Certificates.FiniteK3Dispatch.M4N390To405
import DR.Certificates.FiniteK3Dispatch.M4N406To421
import DR.Certificates.FiniteK3Dispatch.M4N422To437
import DR.Certificates.FiniteK3Dispatch.M4N438To453
import DR.Certificates.FiniteK3Dispatch.M4N454To469
import DR.Certificates.FiniteK3Dispatch.M4N470To485
import DR.Certificates.FiniteK3Dispatch.M4N486To501
import DR.Certificates.FiniteK3Dispatch.M4N502To517
import DR.Certificates.FiniteK3Dispatch.M4N518To533
import DR.Certificates.FiniteK3Dispatch.M4N534To549
import DR.Certificates.FiniteK3Dispatch.M4N550To565
import DR.Certificates.FiniteK3Dispatch.M4N566To581
import DR.Certificates.FiniteK3Dispatch.M4N582To597
import DR.Certificates.FiniteK3Dispatch.M4N598To613
import DR.Certificates.FiniteK3Dispatch.M4N614To629
import DR.Certificates.FiniteK3Dispatch.M4N630To645
import DR.Certificates.FiniteK3Dispatch.M4N646To661
import DR.Certificates.FiniteK3Dispatch.M4N662To677
import DR.Certificates.FiniteK3Dispatch.M4N678To693
import DR.Certificates.FiniteK3Dispatch.M4N694To709
import DR.Certificates.FiniteK3Dispatch.M4N710To725
import DR.Certificates.FiniteK3Dispatch.M4N726To741
import DR.Certificates.FiniteK3Dispatch.M4N742To757
import DR.Certificates.FiniteK3Dispatch.M4N758To773
import DR.Certificates.FiniteK3Dispatch.M4N774To789
import DR.Certificates.FiniteK3Dispatch.M4N790To805
import DR.Certificates.FiniteK3Dispatch.M4N806To821
import DR.Certificates.FiniteK3Dispatch.M4N822To837
import DR.Certificates.FiniteK3Dispatch.M4N838To853
import DR.Certificates.FiniteK3Dispatch.M4N854To869
import DR.Certificates.FiniteK3Dispatch.M4N870To885
import DR.Certificates.FiniteK3Dispatch.M4N886To901
import DR.Certificates.FiniteK3Dispatch.M4N902To917
import DR.Certificates.FiniteK3Dispatch.M4N918To933
import DR.Certificates.FiniteK3Dispatch.M4N934To949
import DR.Certificates.FiniteK3Dispatch.M4N950To959
import DR.Certificates.FiniteK3EnvelopeSoundness

/-! Generated exact finite-strip assembly; every referenced certificate is required. -/
namespace DittertRybin

theorem uniformMaximizer_orderThree_finite_4 {n : ℕ}
    (hlo : 6 ≤ n) (hhi : n ≤ 959) : UniformMaximizer 4 n 3 := by
  by_cases h21 : n ≤ 21
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N6To21.exists_valid n (by omega) h21
    exact hv.uniformMaximizer (by omega)
  by_cases h37 : n ≤ 37
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N22To37.exists_valid n (by omega) h37
    exact hv.uniformMaximizer (by omega)
  by_cases h53 : n ≤ 53
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N38To53.exists_valid n (by omega) h53
    exact hv.uniformMaximizer (by omega)
  by_cases h69 : n ≤ 69
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N54To69.exists_valid n (by omega) h69
    exact hv.uniformMaximizer (by omega)
  by_cases h85 : n ≤ 85
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N70To85.exists_valid n (by omega) h85
    exact hv.uniformMaximizer (by omega)
  by_cases h101 : n ≤ 101
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N86To101.exists_valid n (by omega) h101
    exact hv.uniformMaximizer (by omega)
  by_cases h117 : n ≤ 117
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N102To117.exists_valid n (by omega) h117
    exact hv.uniformMaximizer (by omega)
  by_cases h133 : n ≤ 133
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N118To133.exists_valid n (by omega) h133
    exact hv.uniformMaximizer (by omega)
  by_cases h149 : n ≤ 149
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N134To149.exists_valid n (by omega) h149
    exact hv.uniformMaximizer (by omega)
  by_cases h165 : n ≤ 165
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N150To165.exists_valid n (by omega) h165
    exact hv.uniformMaximizer (by omega)
  by_cases h181 : n ≤ 181
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N166To181.exists_valid n (by omega) h181
    exact hv.uniformMaximizer (by omega)
  by_cases h197 : n ≤ 197
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N182To197.exists_valid n (by omega) h197
    exact hv.uniformMaximizer (by omega)
  by_cases h213 : n ≤ 213
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N198To213.exists_valid n (by omega) h213
    exact hv.uniformMaximizer (by omega)
  by_cases h229 : n ≤ 229
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N214To229.exists_valid n (by omega) h229
    exact hv.uniformMaximizer (by omega)
  by_cases h245 : n ≤ 245
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N230To245.exists_valid n (by omega) h245
    exact hv.uniformMaximizer (by omega)
  by_cases h261 : n ≤ 261
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N246To261.exists_valid n (by omega) h261
    exact hv.uniformMaximizer (by omega)
  by_cases h277 : n ≤ 277
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N262To277.exists_valid n (by omega) h277
    exact hv.uniformMaximizer (by omega)
  by_cases h293 : n ≤ 293
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N278To293.exists_valid n (by omega) h293
    exact hv.uniformMaximizer (by omega)
  by_cases h309 : n ≤ 309
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N294To309.exists_valid n (by omega) h309
    exact hv.uniformMaximizer (by omega)
  by_cases h325 : n ≤ 325
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N310To325.exists_valid n (by omega) h325
    exact hv.uniformMaximizer (by omega)
  by_cases h341 : n ≤ 341
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N326To341.exists_valid n (by omega) h341
    exact hv.uniformMaximizer (by omega)
  by_cases h357 : n ≤ 357
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N342To357.exists_valid n (by omega) h357
    exact hv.uniformMaximizer (by omega)
  by_cases h373 : n ≤ 373
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N358To373.exists_valid n (by omega) h373
    exact hv.uniformMaximizer (by omega)
  by_cases h389 : n ≤ 389
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N374To389.exists_valid n (by omega) h389
    exact hv.uniformMaximizer (by omega)
  by_cases h405 : n ≤ 405
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N390To405.exists_valid n (by omega) h405
    exact hv.uniformMaximizer (by omega)
  by_cases h421 : n ≤ 421
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N406To421.exists_valid n (by omega) h421
    exact hv.uniformMaximizer (by omega)
  by_cases h437 : n ≤ 437
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N422To437.exists_valid n (by omega) h437
    exact hv.uniformMaximizer (by omega)
  by_cases h453 : n ≤ 453
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N438To453.exists_valid n (by omega) h453
    exact hv.uniformMaximizer (by omega)
  by_cases h469 : n ≤ 469
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N454To469.exists_valid n (by omega) h469
    exact hv.uniformMaximizer (by omega)
  by_cases h485 : n ≤ 485
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N470To485.exists_valid n (by omega) h485
    exact hv.uniformMaximizer (by omega)
  by_cases h501 : n ≤ 501
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N486To501.exists_valid n (by omega) h501
    exact hv.uniformMaximizer (by omega)
  by_cases h517 : n ≤ 517
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N502To517.exists_valid n (by omega) h517
    exact hv.uniformMaximizer (by omega)
  by_cases h533 : n ≤ 533
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N518To533.exists_valid n (by omega) h533
    exact hv.uniformMaximizer (by omega)
  by_cases h549 : n ≤ 549
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N534To549.exists_valid n (by omega) h549
    exact hv.uniformMaximizer (by omega)
  by_cases h565 : n ≤ 565
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N550To565.exists_valid n (by omega) h565
    exact hv.uniformMaximizer (by omega)
  by_cases h581 : n ≤ 581
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N566To581.exists_valid n (by omega) h581
    exact hv.uniformMaximizer (by omega)
  by_cases h597 : n ≤ 597
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N582To597.exists_valid n (by omega) h597
    exact hv.uniformMaximizer (by omega)
  by_cases h613 : n ≤ 613
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N598To613.exists_valid n (by omega) h613
    exact hv.uniformMaximizer (by omega)
  by_cases h629 : n ≤ 629
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N614To629.exists_valid n (by omega) h629
    exact hv.uniformMaximizer (by omega)
  by_cases h645 : n ≤ 645
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N630To645.exists_valid n (by omega) h645
    exact hv.uniformMaximizer (by omega)
  by_cases h661 : n ≤ 661
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N646To661.exists_valid n (by omega) h661
    exact hv.uniformMaximizer (by omega)
  by_cases h677 : n ≤ 677
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N662To677.exists_valid n (by omega) h677
    exact hv.uniformMaximizer (by omega)
  by_cases h693 : n ≤ 693
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N678To693.exists_valid n (by omega) h693
    exact hv.uniformMaximizer (by omega)
  by_cases h709 : n ≤ 709
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N694To709.exists_valid n (by omega) h709
    exact hv.uniformMaximizer (by omega)
  by_cases h725 : n ≤ 725
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N710To725.exists_valid n (by omega) h725
    exact hv.uniformMaximizer (by omega)
  by_cases h741 : n ≤ 741
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N726To741.exists_valid n (by omega) h741
    exact hv.uniformMaximizer (by omega)
  by_cases h757 : n ≤ 757
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N742To757.exists_valid n (by omega) h757
    exact hv.uniformMaximizer (by omega)
  by_cases h773 : n ≤ 773
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N758To773.exists_valid n (by omega) h773
    exact hv.uniformMaximizer (by omega)
  by_cases h789 : n ≤ 789
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N774To789.exists_valid n (by omega) h789
    exact hv.uniformMaximizer (by omega)
  by_cases h805 : n ≤ 805
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N790To805.exists_valid n (by omega) h805
    exact hv.uniformMaximizer (by omega)
  by_cases h821 : n ≤ 821
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N806To821.exists_valid n (by omega) h821
    exact hv.uniformMaximizer (by omega)
  by_cases h837 : n ≤ 837
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N822To837.exists_valid n (by omega) h837
    exact hv.uniformMaximizer (by omega)
  by_cases h853 : n ≤ 853
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N838To853.exists_valid n (by omega) h853
    exact hv.uniformMaximizer (by omega)
  by_cases h869 : n ≤ 869
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N854To869.exists_valid n (by omega) h869
    exact hv.uniformMaximizer (by omega)
  by_cases h885 : n ≤ 885
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N870To885.exists_valid n (by omega) h885
    exact hv.uniformMaximizer (by omega)
  by_cases h901 : n ≤ 901
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N886To901.exists_valid n (by omega) h901
    exact hv.uniformMaximizer (by omega)
  by_cases h917 : n ≤ 917
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N902To917.exists_valid n (by omega) h917
    exact hv.uniformMaximizer (by omega)
  by_cases h933 : n ≤ 933
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N918To933.exists_valid n (by omega) h933
    exact hv.uniformMaximizer (by omega)
  by_cases h949 : n ≤ 949
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N934To949.exists_valid n (by omega) h949
    exact hv.uniformMaximizer (by omega)
  obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C4N950To959.exists_valid n (by omega) hhi
  exact hv.uniformMaximizer (by omega)

end DittertRybin
