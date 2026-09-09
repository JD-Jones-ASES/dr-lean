import DR.Certificates.FiniteK4QuinticChecks.Rows00To06
import DR.Certificates.FiniteK4QuinticChecks.Rows07To13
import DR.Certificates.FiniteK4QuinticChecks.Rows14To20
import DR.Certificates.FiniteK4QuinticChecks.Rows21To27
import DR.Certificates.FiniteK4QuinticChecks.Rows28To34
import DR.Certificates.FiniteK4QuinticChecks.Rows35To41
import DR.Certificates.FiniteK4QuinticChecks.Rows42To48
import DR.Certificates.FiniteK4QuinticChecks.Rows49To51

/-! Complete literal 52-by-52 quintic coefficient-pattern gates. -/
namespace DittertRybin.Certificates

theorem finiteK4QuinticPattern_correct : ∀ r c : Fin 52,
    FiniteK4QuinticPatternCorrect r c := by
  intro r
  fin_cases r
  · exact finiteK4QuinticPatternCheck00
  · exact finiteK4QuinticPatternCheck01
  · exact finiteK4QuinticPatternCheck02
  · exact finiteK4QuinticPatternCheck03
  · exact finiteK4QuinticPatternCheck04
  · exact finiteK4QuinticPatternCheck05
  · exact finiteK4QuinticPatternCheck06
  · exact finiteK4QuinticPatternCheck07
  · exact finiteK4QuinticPatternCheck08
  · exact finiteK4QuinticPatternCheck09
  · exact finiteK4QuinticPatternCheck10
  · exact finiteK4QuinticPatternCheck11
  · exact finiteK4QuinticPatternCheck12
  · exact finiteK4QuinticPatternCheck13
  · exact finiteK4QuinticPatternCheck14
  · exact finiteK4QuinticPatternCheck15
  · exact finiteK4QuinticPatternCheck16
  · exact finiteK4QuinticPatternCheck17
  · exact finiteK4QuinticPatternCheck18
  · exact finiteK4QuinticPatternCheck19
  · exact finiteK4QuinticPatternCheck20
  · exact finiteK4QuinticPatternCheck21
  · exact finiteK4QuinticPatternCheck22
  · exact finiteK4QuinticPatternCheck23
  · exact finiteK4QuinticPatternCheck24
  · exact finiteK4QuinticPatternCheck25
  · exact finiteK4QuinticPatternCheck26
  · exact finiteK4QuinticPatternCheck27
  · exact finiteK4QuinticPatternCheck28
  · exact finiteK4QuinticPatternCheck29
  · exact finiteK4QuinticPatternCheck30
  · exact finiteK4QuinticPatternCheck31
  · exact finiteK4QuinticPatternCheck32
  · exact finiteK4QuinticPatternCheck33
  · exact finiteK4QuinticPatternCheck34
  · exact finiteK4QuinticPatternCheck35
  · exact finiteK4QuinticPatternCheck36
  · exact finiteK4QuinticPatternCheck37
  · exact finiteK4QuinticPatternCheck38
  · exact finiteK4QuinticPatternCheck39
  · exact finiteK4QuinticPatternCheck40
  · exact finiteK4QuinticPatternCheck41
  · exact finiteK4QuinticPatternCheck42
  · exact finiteK4QuinticPatternCheck43
  · exact finiteK4QuinticPatternCheck44
  · exact finiteK4QuinticPatternCheck45
  · exact finiteK4QuinticPatternCheck46
  · exact finiteK4QuinticPatternCheck47
  · exact finiteK4QuinticPatternCheck48
  · exact finiteK4QuinticPatternCheck49
  · exact finiteK4QuinticPatternCheck50
  · exact finiteK4QuinticPatternCheck51

end DittertRybin.Certificates
