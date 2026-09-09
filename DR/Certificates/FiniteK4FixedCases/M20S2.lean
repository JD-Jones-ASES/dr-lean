import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 20×20, seed 2.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M20S2
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 5 :=
  #v[(76876191/20000000),(738887811506223/405735452500000),(516415700311325954216951/88666537380746760000000),(363955232537798827128355003351179/196237966118303862602441380000000),(2251934657447392947738210160160872846594013/2096382139417721244259324819302791040000000)]
def principalFactor : Vector (Vector ℚ 5) 5 :=
  #v[#v[1,(-633308/8541799),(-72002621/76876191),(-5886757/76876191),(-70140331/263575512)],#v[0,1,(-502466733562613/2955551246024892),(369321049823/40487003370204),(984735751711747/35466614952298704)],#v[0,0,1,(-30919307643669653249249/516415700311325954216951),(-689433617296608772896295/6196988403735911450603412)],#v[0,0,0,1,(158564312502703925320786150383229/8734925580907171851080520080428296)],#v[0,0,0,0,1]]
def principalGram : GramCertificate 5 5 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 2 :=
  #v[(622617383/40000000),(49013215132655002373/17034811598880000000)]
def rowFactor : Vector (Vector ℚ 2) 2 :=
  #v[#v[1,(324493343/3735704298)],#v[0,1]]
def rowGram : GramCertificate 2 2 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 3 :=
  #v[(43622377/2500000),(8418227563565653/436223770000000),(6090499776934384870969483/4545842884325452620000000)]
def columnFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(-2242771/174489508),(333915/43622377)],#v[0,1,(72404175052973/16836455127131306)],#v[0,0,1]]
def columnGram : GramCertificate 3 3 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(893605517/60000000)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed20Coefficient 20 20 2).mulVec
      (finiteK4FixedWeight 20 20 2 : Fin (fourRowFiniteSeedFullSize 2) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed20Coefficient 20 20 2) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed20Coefficient 20 2) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed20Coefficient 20 2) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed20Coefficient 2) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M20S2
