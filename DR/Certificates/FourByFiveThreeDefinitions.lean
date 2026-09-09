import DR.Certificates.FourByFiveThreeData
import DR.Certificates.FiniteK3Orbits
import Mathlib.Logic.Equiv.Fin.Basic

/-! The source's physical 4x5 matrices use the complete checked 93-role entry map. -/
namespace DittertRybin.Certificates
open scoped BigOperators

def fourByFiveThreeCell : (Fin 4 × Fin 5) ≃ Fin 20 := finProdFinEquiv

def fourByFiveThreeCoefficient (i : Fin 93) : ℚ := (fourByFiveThreeNumerators.get i:ℚ)/200

def fourByFiveThreeMultiplier (s : Fin 4) : Fin 20 := ![0,1,5,6] s

def fourByFiveThreeMatrix (e f : Fin 20) : Matrix (Fin 20) (Fin 20) ℚ :=
  fun a b => finiteK3Entry fourByFiveThreeCoefficient
    (fourByFiveThreeCell.symm e) (fourByFiveThreeCell.symm f)
    (fourByFiveThreeCell.symm a) (fourByFiveThreeCell.symm b)

def fourByFiveThreeSeed (s : Fin 4) : Matrix (Fin 20) (Fin 20) ℚ :=
  fourByFiveThreeMatrix 0 (fourByFiveThreeMultiplier s)

def fourByFiveThreeShift (s : Fin 4) : Matrix (Fin 20) (Fin 20) ℚ :=
  fourByFiveThreeSeed s-(2/5:ℚ) • centeringMatrix 20

def fourByFiveThreeGram (s : Fin 4) : GramCertificate 19 19 :=
  ⟨fun i => (fourByFiveThreeWeights.get s).get i,
    fun i j => ((fourByFiveThreeFactors.get s).get i).get j⟩

theorem fourByFiveThreeMatrix_symmetric (e f a b : Fin 20) :
    fourByFiveThreeMatrix e f a b=fourByFiveThreeMatrix e f b a :=
  (finiteK3Entry_symmetric _ _ _ _ _).symm

end DittertRybin.Certificates
