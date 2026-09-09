import DR.Certificates.FiniteK3OrbitData

/-! Exact compressed lookups; all 82 values are independently checked in Lean. -/
namespace DittertRybin.Certificates

def fourByFiveThreeRowPatterns : Vector (Vector (Vector (Fin 15) 4) 4) 2 :=
  #v[#v[#v[0,1,1,1],#v[2,3,4,4],#v[2,4,3,4],#v[2,4,4,3]],#v[#v[5,6,7,7],#v[8,9,10,10],#v[11,12,13,14],#v[11,12,14,13]]]

def fourByFiveThreeColPatterns : Vector (Vector (Vector (Fin 15) 5) 5) 2 :=
  #v[#v[#v[0,1,1,1,1],#v[2,3,4,4,4],#v[2,4,3,4,4],#v[2,4,4,3,4],#v[2,4,4,4,3]],#v[#v[5,6,7,7,7],#v[8,9,10,10,10],#v[11,12,13,14,14],#v[11,12,14,13,14],#v[11,12,14,14,13]]]

end DittertRybin.Certificates
