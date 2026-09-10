import DR.Certificates.ConsecutiveCutRational

namespace DittertRybin.Certificates

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All 404 non-whole positive cuts in this exact finite dimension. -/
theorem consecutiveCutCertificate27 :
    ∀ k : Fin 28, ∀ l : Fin 29, ConsecutiveCutCertificate 27 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
