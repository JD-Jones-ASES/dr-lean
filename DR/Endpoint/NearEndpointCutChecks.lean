import DR.Endpoint.NearEndpointCutGate21
import DR.Endpoint.NearEndpointCutGate22
import DR.Endpoint.NearEndpointCutGate23
import DR.Endpoint.NearEndpointCutGate24
import DR.Endpoint.NearEndpointCutGate25
import Mathlib.Tactic.IntervalCases

/-! Complete exact coverage of all1,380 positive non-whole ordered cut
sizes and all five cubic brackets. These are scalar certificates; their
permanent-floor interpretation is deliberately a separate theorem. -/
namespace DittertRybin.Certificates
open scoped BigOperators

 theorem nearEndpointBracketCertificate_checked {n : ℕ} (hn : 21≤n) (hn' : n≤25) :
    NearEndpointBracketCertificate n := by
  interval_cases n
  · exact nearEndpointBracketCertificate21
  · exact nearEndpointBracketCertificate22
  · exact nearEndpointBracketCertificate23
  · exact nearEndpointBracketCertificate24
  · exact nearEndpointBracketCertificate25

 theorem nearEndpointCutCertificate_checked {n k l : ℕ} (hn : 21≤n) (hn' : n≤25)
    (hk : k≤n) (hl : l≤n) : NearEndpointCutCertificate n k l := by
  interval_cases n
  · exact nearEndpointCutCertificate21 ⟨k,by omega⟩ ⟨l,by omega⟩
  · exact nearEndpointCutCertificate22 ⟨k,by omega⟩ ⟨l,by omega⟩
  · exact nearEndpointCutCertificate23 ⟨k,by omega⟩ ⟨l,by omega⟩
  · exact nearEndpointCutCertificate24 ⟨k,by omega⟩ ⟨l,by omega⟩
  · exact nearEndpointCutCertificate25 ⟨k,by omega⟩ ⟨l,by omega⟩

/-- The integer enumeration counts the full ordered domain, with no omitted
orientation or diagonal cut-size pair. -/
theorem nearEndpoint_finite_cut_coverage :
    (∑ n ∈ Finset.Icc 21 25,
      ((Finset.range (n+1) ×ˢ Finset.range (n+1)).filter fun kl =>
        n<kl.1+kl.2 ∧ (kl.1≠n ∨ kl.2≠n)).card)=1380 := by
  decide +kernel

end DittertRybin.Certificates
