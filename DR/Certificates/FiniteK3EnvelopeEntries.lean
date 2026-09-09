import DR.Certificates.FiniteK3Orbits
import DR.Certificates.FiniteK3EnvelopePatternData

/-! A fixed 9x4 virtual board contains every small-block entry in the finite
K3 envelope. All lookups are checked against the actual 93-role entry map. -/
namespace DittertRybin.Certificates

def finiteK3EnvelopeRowMode (s : Fin 4) : Fin 2 := ⟨s.val/2,by omega⟩
def finiteK3EnvelopeColMode (s : Fin 4) : Fin 2 := ⟨s.val%2,by omega⟩

def finiteK3DistinguishedColumns (s : Fin 4) : Nat := s.val%2+1

def finiteK3FirstCell (m : Nat) (hm : 2≤m) (s : Fin 4) :
    Fin m × Fin (finiteK3DistinguishedColumns s) :=
  (⟨0,by omega⟩,⟨0,by unfold finiteK3DistinguishedColumns; omega⟩)

def finiteK3SecondCell (m : Nat) (hm : 2≤m) (s : Fin 4) :
    Fin m × Fin (finiteK3DistinguishedColumns s) :=
  (⟨s.val/2,by omega⟩,⟨s.val%2,by unfold finiteK3DistinguishedColumns; omega⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem finiteK3EnvelopeRowPatterns_checked : ∀ (t : Fin 2) (a b : Fin 9),
    fourTuplePatternIndex (![0,t.castLE (by decide),a,b] : Fin 4 → Fin 9)=
      ((finiteK3EnvelopeRowPatterns.get t).get a).get b := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem finiteK3EnvelopeColPatterns_checked : ∀ (t : Fin 2) (a b : Fin 4),
    fourTuplePatternIndex (![0,t.castLE (by decide),a,b] : Fin 4 → Fin 4)=
      ((finiteK3EnvelopeColPatterns.get t).get a).get b := by
  decide +kernel

def finiteK3EnvelopeEntry {R : Type*} (coeff : Fin 93 → R) (s : Fin 4)
    (a b : Fin 9 × Fin 4) : R :=
  coeff (finiteK3TableRole
    (((finiteK3EnvelopeRowPatterns.get (finiteK3EnvelopeRowMode s)).get a.1).get b.1)
    (((finiteK3EnvelopeColPatterns.get (finiteK3EnvelopeColMode s)).get a.2).get b.2))

theorem finiteK3EnvelopeEntry_eq {R : Type*} (coeff : Fin 93 → R) (s : Fin 4)
    (a b : Fin 9 × Fin 4) :
    finiteK3EnvelopeEntry coeff s a b = finiteK3Entry coeff (0,0)
      ((finiteK3EnvelopeRowMode s).castLE (by decide),
       (finiteK3EnvelopeColMode s).castLE (by decide)) a b := by
  unfold finiteK3Entry finiteK3Role
  rw [finiteK3EnvelopeRowPatterns_checked,finiteK3EnvelopeColPatterns_checked]
  rfl

end DittertRybin.Certificates
