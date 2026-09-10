import DR.Endpoint.NearEndpointCutRational

namespace DittertRybin.Certificates
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact cubic isolation and lower-reference comparison at n=22. -/
theorem nearEndpointBracketCertificate22 : NearEndpointBracketCertificate 22 := by
  decide +kernel

/-- All 252 non-whole positive ordered cut sizes, including both orientations. -/
theorem nearEndpointCutCertificate22 :
    ∀ k l : Fin 23, NearEndpointCutCertificate 22 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
