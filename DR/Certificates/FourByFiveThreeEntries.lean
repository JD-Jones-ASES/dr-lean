import DR.Certificates.FourByFiveThreeDefinitions
import DR.Certificates.FourByFiveThreePatternData

/-! Eighty-two exact one-axis compression checks identify every physical seed entry.
The rational Gram verifier can then use the compact table without recomputing
label compression during each arithmetic operation. -/
namespace DittertRybin.Certificates

def fourByFiveThreeRowMode (s : Fin 4) : Fin 2 := ⟨s.val/2,by omega⟩
def fourByFiveThreeColMode (s : Fin 4) : Fin 2 := ⟨s.val%2,by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem fourByFiveThreeRowPatterns_checked : ∀ (t : Fin 2) (a b : Fin 4),
    fourTuplePatternIndex (![0,t.castLE (by decide),a,b] : Fin 4 → Fin 4)=
      ((fourByFiveThreeRowPatterns.get t).get a).get b := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem fourByFiveThreeColPatterns_checked : ∀ (t : Fin 2) (a b : Fin 5),
    fourTuplePatternIndex (![0,t.castLE (by decide),a,b] : Fin 4 → Fin 5)=
      ((fourByFiveThreeColPatterns.get t).get a).get b := by
  decide +kernel

theorem fourByFiveThreeMultiplier_modes : ∀ s : Fin 4,
    (fourByFiveThreeCell.symm (fourByFiveThreeMultiplier s)).1=(fourByFiveThreeRowMode s).castLE (by decide) ∧
    (fourByFiveThreeCell.symm (fourByFiveThreeMultiplier s)).2=(fourByFiveThreeColMode s).castLE (by decide) := by
  decide +kernel

def fourByFiveThreeTableMatrix (s : Fin 4) : Matrix (Fin 20) (Fin 20) ℚ := fun i j =>
  fourByFiveThreeCoefficient (finiteK3TableRole
    (((fourByFiveThreeRowPatterns.get (fourByFiveThreeRowMode s)).get
      (fourByFiveThreeCell.symm i).1).get (fourByFiveThreeCell.symm j).1)
    (((fourByFiveThreeColPatterns.get (fourByFiveThreeColMode s)).get
      (fourByFiveThreeCell.symm i).2).get (fourByFiveThreeCell.symm j).2))

theorem fourByFiveThreeSeed_eq_table (s : Fin 4) :
    fourByFiveThreeSeed s=fourByFiveThreeTableMatrix s := by
  ext i j
  unfold fourByFiveThreeSeed fourByFiveThreeMatrix finiteK3Entry finiteK3Role
  have hzero : fourByFiveThreeCell.symm 0=(0,0) := rfl
  rw [hzero]
  simp only [fourByFiveThreeMultiplier_modes s]
  rw [fourByFiveThreeRowPatterns_checked,fourByFiveThreeColPatterns_checked]
  rfl

def fourByFiveThreeTableShift (s : Fin 4) : Matrix (Fin 20) (Fin 20) ℚ :=
  fourByFiveThreeTableMatrix s-(2/5:ℚ) • centeringMatrix 20

theorem fourByFiveThreeShift_eq_table (s : Fin 4) :
    fourByFiveThreeShift s=fourByFiveThreeTableShift s := by
  rw [fourByFiveThreeShift,fourByFiveThreeSeed_eq_table]
  rfl

end DittertRybin.Certificates
