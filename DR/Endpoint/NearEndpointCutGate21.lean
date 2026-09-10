import DR.Endpoint.NearEndpointCutRational

namespace DittertRybin.Certificates
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact cubic isolation and lower-reference comparison at n=21. -/
theorem nearEndpointBracketCertificate21 : NearEndpointBracketCertificate 21 := by
  decide +kernel

/-- All 230 non-whole positive ordered cut sizes, including both orientations. -/
theorem nearEndpointCutCertificate21 :
    ∀ k l : Fin 22, NearEndpointCutCertificate 21 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
