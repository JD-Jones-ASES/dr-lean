import DR.Certificates.ConsecutiveCutRational

namespace DittertRybin.Certificates

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All 251 non-whole positive cuts in this exact finite dimension. -/
theorem consecutiveCutCertificate21 :
    ∀ k : Fin 22, ∀ l : Fin 23, ConsecutiveCutCertificate 21 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
