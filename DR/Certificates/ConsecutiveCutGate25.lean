import DR.Certificates.ConsecutiveCutRational

namespace DittertRybin.Certificates

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All 349 non-whole positive cuts in this exact finite dimension. -/
theorem consecutiveCutCertificate25 :
    ∀ k : Fin 26, ∀ l : Fin 27, ConsecutiveCutCertificate 25 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
