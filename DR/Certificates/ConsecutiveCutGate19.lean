import DR.Certificates.ConsecutiveCutRational

namespace DittertRybin.Certificates

set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- All208 non-whole positive cuts at the first finite dimension. -/
theorem consecutiveCutCertificate19 :
    ∀ k : Fin 20, ∀ l : Fin 21, ConsecutiveCutCertificate 19 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
