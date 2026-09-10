import DR.Endpoint.NearEndpointCutRational

namespace DittertRybin.Certificates
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact cubic isolation and lower-reference comparison at n=25. -/
theorem nearEndpointBracketCertificate25 : NearEndpointBracketCertificate 25 := by
  decide +kernel

/-- All 324 non-whole positive ordered cut sizes, including both orientations. -/
theorem nearEndpointCutCertificate25 :
    ∀ k l : Fin 26, NearEndpointCutCertificate 25 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
