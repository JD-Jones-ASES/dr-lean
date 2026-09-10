import DR.Certificates.ConsecutiveCutRational

namespace DittertRybin.Certificates

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All 229 non-whole positive cuts in this exact finite dimension. -/
theorem consecutiveCutCertificate20 :
    ∀ k : Fin 21, ∀ l : Fin 22, ConsecutiveCutCertificate 20 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
