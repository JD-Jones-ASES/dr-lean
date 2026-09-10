import DR.Certificates.ConsecutiveCutRational

namespace DittertRybin.Certificates

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All 463 non-whole positive cuts in this exact finite dimension. -/
theorem consecutiveCutCertificate29 :
    ∀ k : Fin 30, ∀ l : Fin 31, ConsecutiveCutCertificate 29 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
