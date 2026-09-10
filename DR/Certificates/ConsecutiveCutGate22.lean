import DR.Certificates.ConsecutiveCutRational

namespace DittertRybin.Certificates

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All 274 non-whole positive cuts in this exact finite dimension. -/
theorem consecutiveCutCertificate22 :
    ∀ k : Fin 23, ∀ l : Fin 24, ConsecutiveCutCertificate 22 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
