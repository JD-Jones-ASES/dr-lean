import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 5×5, seed 2.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M5S2
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 5 :=
  #v[(100687/62500),(118103599/80549600),(2296142385307/944828792000),(47547807792171681/45922847706140000),(82282223964085045544389/111440174512902377343750)]
def principalFactor : Vector (Vector ℚ 5) 5 :=
  #v[#v[1,(-5625/100687),(-248925/402748),(4695/201374),(-30401/402748)],#v[0,1,(122183282/590517995),(-268089877/590517995),(-38177914/590517995)],#v[0,0,1,(2900358241834/11480711926535),(601720398291/57403559632675)],#v[0,0,0,1,(-412795631999776328/1188695194804292025)],#v[0,0,0,0,1]]
def principalGram : GramCertificate 5 5 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 2 :=
  #v[(5054861/750000),(192728872139/216636900000)]
def rowFactor : Vector (Vector ℚ 2) 2 :=
  #v[#v[1,(377305/722123)],#v[0,1]]
def rowGram : GramCertificate 2 2 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 3 :=
  #v[(3297/1000),(148926431/82425000),(73830259609801/33508446975000)]
def columnFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(2449/3297),(177/1099)],#v[0,1,(-19652175/148926431)],#v[0,0,1]]
def columnGram : GramCertificate 3 3 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(62627/75000)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 2).mulVec
      (finiteK4FixedWeight 5 5 2 : Fin (fourRowFiniteSeedFullSize 2) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed5Coefficient 5 5 2) := by
  refine ⟨⟨?_,?_⟩,?_,?_,?_⟩
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed5Coefficient 5 2) := by
  refine ⟨⟨?_,?_⟩,?_,?_,?_⟩
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed5Coefficient 5 2) := by
  refine ⟨⟨?_,?_⟩,?_,?_,?_⟩
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel
  · intro i j
    fin_cases i <;> fin_cases j <;> decide +kernel
  · intro i
    fin_cases i <;> decide +kernel

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed5Coefficient 2) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M5S2
