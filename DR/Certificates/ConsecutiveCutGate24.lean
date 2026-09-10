import DR.Certificates.ConsecutiveCutRational

namespace DittertRybin.Certificates

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All 323 non-whole positive cuts in this exact finite dimension. -/
theorem consecutiveCutCertificate24 :
    ∀ k : Fin 25, ∀ l : Fin 26, ConsecutiveCutCertificate 24 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
