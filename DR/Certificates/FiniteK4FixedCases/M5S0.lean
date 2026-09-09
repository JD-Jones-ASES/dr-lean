import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 5×5, seed 0.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M5S0
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 3 :=
  #v[(5424/15625),(196901279/216960000),(44018954469446/76914562109375)]
def principalFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(1877/43392),(7793/43392)],#v[0,1,(-1462282213/4922531975)],#v[0,0,1]]
def principalGram : GramCertificate 3 3 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 2 :=
  #v[(105673/46875),(98171265953/105673000000)]
def rowFactor : Vector (Vector ℚ 2) 2 :=
  #v[#v[1,(359185/845384)],#v[0,1]]
def rowGram : GramCertificate 2 2 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 2 :=
  #v[(92311/37500),(1361202986659/1384665000000)]
def columnFactor : Vector (Vector ℚ 2) 2 :=
  #v[#v[1,(682341/1846220)],#v[0,1]]
def columnGram : GramCertificate 2 2 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(130603/93750)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 0).mulVec
      (finiteK4FixedWeight 5 5 0 : Fin (fourRowFiniteSeedFullSize 0) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed5Coefficient 5 5 0) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed5Coefficient 5 0) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed5Coefficient 5 0) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed5Coefficient 0) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M5S0
