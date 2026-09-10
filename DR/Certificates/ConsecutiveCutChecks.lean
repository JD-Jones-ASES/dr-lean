import DR.Certificates.ConsecutiveCutGate19
import DR.Certificates.ConsecutiveCutGate20
import DR.Certificates.ConsecutiveCutGate21
import DR.Certificates.ConsecutiveCutGate22
import DR.Certificates.ConsecutiveCutGate23
import DR.Certificates.ConsecutiveCutGate24
import DR.Certificates.ConsecutiveCutGate25
import DR.Certificates.ConsecutiveCutGate26
import DR.Certificates.ConsecutiveCutGate27
import DR.Certificates.ConsecutiveCutGate28
import DR.Certificates.ConsecutiveCutGate29

/-! Exhaustive exact rational verification over the eleven literal dimensions.
The tables are formula-defined, and each gate is replayed by the Lean kernel. -/

namespace DittertRybin.Certificates

theorem consecutiveCutCertificate_checked {m k l : ℕ}
    (hm : 19 ≤ m) (hm' : m ≤ 29) (hk : k ≤ m) (hl : l ≤ m+1) :
    ConsecutiveCutCertificate m k l := by
  interval_cases m
  · exact consecutiveCutCertificate19 ⟨k, by omega⟩ ⟨l, by omega⟩
  · exact consecutiveCutCertificate20 ⟨k, by omega⟩ ⟨l, by omega⟩
  · exact consecutiveCutCertificate21 ⟨k, by omega⟩ ⟨l, by omega⟩
  · exact consecutiveCutCertificate22 ⟨k, by omega⟩ ⟨l, by omega⟩
  · exact consecutiveCutCertificate23 ⟨k, by omega⟩ ⟨l, by omega⟩
  · exact consecutiveCutCertificate24 ⟨k, by omega⟩ ⟨l, by omega⟩
  · exact consecutiveCutCertificate25 ⟨k, by omega⟩ ⟨l, by omega⟩
  · exact consecutiveCutCertificate26 ⟨k, by omega⟩ ⟨l, by omega⟩
  · exact consecutiveCutCertificate27 ⟨k, by omega⟩ ⟨l, by omega⟩
  · exact consecutiveCutCertificate28 ⟨k, by omega⟩ ⟨l, by omega⟩
  · exact consecutiveCutCertificate29 ⟨k, by omega⟩ ⟨l, by omega⟩

theorem consecutiveCut_row_cap_checked {m : ℕ} (hm : 19 ≤ m) (hm' : m ≤ 29) :
    (m : ℚ)*consecutiveAvoidanceRat m (m+1) /
      (2*(1-consecutiveAvoidanceRat m (m+1))) ≤ (101/100-1 : ℚ)^2 := by
  interval_cases m <;> decide +kernel

end DittertRybin.Certificates
