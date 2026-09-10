import DR.Endpoint.NearEndpointCutRational

namespace DittertRybin.Certificates
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Exact cubic isolation and lower-reference comparison at n=24. -/
theorem nearEndpointBracketCertificate24 : NearEndpointBracketCertificate 24 := by
  decide +kernel

/-- All 299 non-whole positive ordered cut sizes, including both orientations. -/
theorem nearEndpointCutCertificate24 :
    ∀ k l : Fin 25, NearEndpointCutCertificate 24 k.val l.val := by
  decide +kernel

end DittertRybin.Certificates
