import DR.Rectangular.FourRowFiniteDataFastPattern
import DR.Rectangular.FourRowFiniteSeeds
import DR.Certificates.FiniteK4Orbits

/-! A proved fast evaluator for the actual role key, reusing the complete Bell-five catalogue. -/

namespace DittertRybin
open Certificates
noncomputable section

def fourRowFiniteFastPatternIndex {α : Type*} [DecidableEq α] (s : Fin 5 → α) : Fin 52 :=
  fourRowFinitePatternLookup (fourRowFinitePatternCode (tupleFirstIndex s))

theorem fourRowFiniteFastPatternIndex_eq {α : Type*} [DecidableEq α] (s : Fin 5 → α) :
    fourRowFiniteFastPatternIndex s = fiveTuplePatternIndex s := by
  unfold fourRowFiniteFastPatternIndex
  rw [← fiveTuplePatternIndex_spec, fourRowFinitePatternLookup_correct]

def fourRowFiniteFastRoleKey (s : Fin 5 → ℕ × ℕ) : ℕ :=
  finiteK4RoleKeys.get ((finiteK4RoleTable.get
    (fourRowFiniteFastPatternIndex (fun i => (s i).1))).get
      (fourRowFiniteFastPatternIndex (fun i => (s i).2)))

theorem fourRowFiniteFastRoleKey_eq (s : Fin 5 → ℕ × ℕ) :
    fourRowFiniteFastRoleKey s = finiteK4TupleRoleKey s := by
  simp only [fourRowFiniteFastRoleKey, fourRowFiniteFastPatternIndex_eq, finiteK4RoleIndex_spec,
    finiteK4RoleIndex]

def fourRowFiniteSeedFastKey (s : Fin 10) (x y : ℕ × ℕ) : ℕ :=
  fourRowFiniteFastRoleKey ![(fourRowFiniteSeedMark s).getD 0 (0,0),
    (fourRowFiniteSeedMark s).getD 1 (0,0), (fourRowFiniteSeedMark s).getD 2 (0,0), x, y]

private theorem fourRowFiniteSeedMark_three : ∀ s : Fin 10,
    [(fourRowFiniteSeedMark s).getD 0 (0,0), (fourRowFiniteSeedMark s).getD 1 (0,0),
      (fourRowFiniteSeedMark s).getD 2 (0,0)] = fourRowFiniteSeedMark s := by
  decide +kernel

theorem fourRowFiniteSeedFastKey_eq (s : Fin 10) (x y : ℕ × ℕ) :
    fourRowFiniteSeedFastKey s x y = fourRowFiniteCanonicalRoleKey (fourRowFiniteSeedMark s) x y := by
  rw [fourRowFiniteSeedFastKey, fourRowFiniteFastRoleKey_eq]
  change fourRowFiniteCanonicalRoleKey
    [(fourRowFiniteSeedMark s).getD 0 (0,0), (fourRowFiniteSeedMark s).getD 1 (0,0),
      (fourRowFiniteSeedMark s).getD 2 (0,0)] x y = _
  rw [fourRowFiniteSeedMark_three]

end
end DittertRybin
