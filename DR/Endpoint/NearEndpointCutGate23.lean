import DR.Endpoint.NearEndpointCutRational

namespace DittertRybin.Certificates
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact cubic isolation and lower-reference comparison at n=23. -/
theorem nearEndpointBracketCertificate23 : NearEndpointBracketCertificate 23 := by
  decide +kernel

/-- All 275 non-whole positive ordered cut sizes, including both orientations. -/
theorem nearEndpointCutCertificate23 :
    ∀ k l : Fin 24, NearEndpointCutCertificate 23 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
