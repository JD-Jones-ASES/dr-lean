import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 20×20, seed 1.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M20S1
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 5 :=
  #v[(479619589/80000000),(254290422429944523/38369567120000000),(13142660459445614652694957/10171616897197780920000000),(55129018268927102391477237513553969/28388146592402527649821107120000000),(164094030030660520563234958787430536918002623/83796107768769195635045401020602032880000000)]
def principalFactor : Vector (Vector ℚ 5) 5 :=
  #v[#v[1,(-344058774/479619589),(-182528393/959239178),(-74969665/959239178),(-77198701/959239178)],#v[0,1,(-39606872132801485/508580844859889046),(-26000749900115869/508580844859889046),(-33712599311764853/508580844859889046)],#v[0,0,1,(557457447511770465599866/13142660459445614652694957),(755566424467044927429374/13142660459445614652694957)],#v[0,0,0,1,(293920666984792943078826504917066/55129018268927102391477237513553969)],#v[0,0,0,0,1]]
def principalGram : GramCertificate 5 5 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 3 :=
  #v[(544161919/30000000),(1780532499855733597/87065907040000000),(617259010092524886474644839/427327799965376063280000000)]
def rowFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(-30308049/2176647676),(29452431/4353295352)],#v[0,1,(-887009211078939/3561064999711467194)],#v[0,0,1]]
def rowGram : GramCertificate 3 3 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 2 :=
  #v[(1882361233/120000000),(54768802802054697893/17167134444960000000)]
def columnFactor : Vector (Vector ℚ 2) 2 :=
  #v[#v[1,(336342649/3764722466)],#v[0,1]]
def columnGram : GramCertificate 2 2 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(1150422/78125)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed20Coefficient 20 20 1).mulVec
      (finiteK4FixedWeight 20 20 1 : Fin (fourRowFiniteSeedFullSize 1) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed20Coefficient 20 20 1) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed20Coefficient 20 1) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed20Coefficient 20 1) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed20Coefficient 1) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M20S1
