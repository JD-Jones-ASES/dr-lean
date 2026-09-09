import DR.Certificates.FiniteK3OrbitData

/-! Generated one-axis lookups; every value is checked against actual label compression. -/
namespace DittertRybin.Certificates

def finiteK3EnvelopeRowPatterns : Vector (Vector (Vector (Fin 15) 9) 9) 2 :=
  #v[#v[#v[0,1,1,1,1,1,1,1,1],#v[2,3,4,4,4,4,4,4,4],#v[2,4,3,4,4,4,4,4,4],#v[2,4,4,3,4,4,4,4,4],#v[2,4,4,4,3,4,4,4,4],#v[2,4,4,4,4,3,4,4,4],#v[2,4,4,4,4,4,3,4,4],#v[2,4,4,4,4,4,4,3,4],#v[2,4,4,4,4,4,4,4,3]],#v[#v[5,6,7,7,7,7,7,7,7],#v[8,9,10,10,10,10,10,10,10],#v[11,12,13,14,14,14,14,14,14],#v[11,12,14,13,14,14,14,14,14],#v[11,12,14,14,13,14,14,14,14],#v[11,12,14,14,14,13,14,14,14],#v[11,12,14,14,14,14,13,14,14],#v[11,12,14,14,14,14,14,13,14],#v[11,12,14,14,14,14,14,14,13]]]

def finiteK3EnvelopeColPatterns : Vector (Vector (Vector (Fin 15) 4) 4) 2 :=
  #v[#v[#v[0,1,1,1],#v[2,3,4,4],#v[2,4,3,4],#v[2,4,4,3]],#v[#v[5,6,7,7],#v[8,9,10,10],#v[11,12,13,14],#v[11,12,14,13]]]

end DittertRybin.Certificates
