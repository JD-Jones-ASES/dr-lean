import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 5×5, seed 1.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M5S1
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 5 :=
  #v[(106603/62500),(3933011038/1665671875),(596302455467/707941986840),(184330104946726092421/149075613866750000000),(632780780765546495999600541/737320419786904369684000000)]
def principalFactor : Vector (Vector ℚ 5) 5 :=
  #v[#v[1,(-86381/106603),(29153/319809),(-68611/852824),(-39859/852824)],#v[0,1,(-284745301/23598066228),(8166596121/62928176608),(367132457/1966505519)],#v[0,0,1,(-368768102002869/2981512277335000),(-474912153912627/1490756138667500)],#v[0,0,0,1,(-88065021241159173739/184330104946726092421)],#v[0,0,0,0,1]]
def principalGram : GramCertificate 5 5 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 3 :=
  #v[(25319/7500),(5744644159/3164875000),(1112250288518159/517017974310000)]
def rowFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(188661/253190),(4173/25319)],#v[0,1,(-736130005/5744644159)],#v[0,0,1]]
def rowGram : GramCertificate 3 3 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 2 :=
  #v[(111637/15625),(79752322371/89309600000)]
def columnFactor : Vector (Vector ℚ 2) 2 :=
  #v[#v[1,(941445/1786192)],#v[0,1]]
def columnGram : GramCertificate 2 2 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(62207/75000)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 1).mulVec
      (finiteK4FixedWeight 5 5 1 : Fin (fourRowFiniteSeedFullSize 1) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed5Coefficient 5 5 1) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed5Coefficient 5 1) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed5Coefficient 5 1) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed5Coefficient 1) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M5S1
