import DR.Certificates.ConsecutiveCutRational

namespace DittertRybin.Certificates

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All 376 non-whole positive cuts in this exact finite dimension. -/
theorem consecutiveCutCertificate26 :
    ∀ k : Fin 27, ∀ l : Fin 28, ConsecutiveCutCertificate 26 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
