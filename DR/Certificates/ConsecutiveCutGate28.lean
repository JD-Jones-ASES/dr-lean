import DR.Certificates.ConsecutiveCutRational

namespace DittertRybin.Certificates

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All 433 non-whole positive cuts in this exact finite dimension. -/
theorem consecutiveCutCertificate28 :
    ∀ k : Fin 29, ∀ l : Fin 30, ConsecutiveCutCertificate 28 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
