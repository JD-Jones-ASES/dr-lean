import DR.Certificates.ConsecutiveCutRational

namespace DittertRybin.Certificates

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All 298 non-whole positive cuts in this exact finite dimension. -/
theorem consecutiveCutCertificate23 :
    ∀ k : Fin 24, ∀ l : Fin 25, ConsecutiveCutCertificate 23 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
