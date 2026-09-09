import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 5×5, seed 4.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M5S4
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 7 :=
  #v[(268838/46875),(72250104619/12601781250),(70915753744/12373265625),(60543009/40482500),(1771018093878984983/1694803154565375000),(54213958775384538885014142961/52881891875988939998386800000),(305195680774618806992563/305471224247310467450000)]
def principalFactor : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(-4875/268838),(-4875/268838),(-3747/134419),(8645/134419),(3750/134419),(3750/134419)],#v[0,1,(-4875/263963),(-7494/263963),(190961250/6568191329),(425888320/6568191329),(7500/263963)],#v[0,0,1,(-3747/129544),(95480625/3223443352),(95480625/3223443352),(210774785/3223443352)],#v[0,0,0,1,(-98385776/908145135),(-98385776/908145135),(-98385776/908145135)],#v[0,0,0,0,1,(-974647890569730583/7084072375515939932),(-974647890569730583/7084072375515939932)],#v[0,0,0,0,0,1,(-974647890569730583/6109424484946209349)],#v[0,0,0,0,0,0,1]]
def principalGram : GramCertificate 7 7 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 4 :=
  #v[(27099/6250),(1220420799/301100000),(734318937/188987500),(1941791743/682275000)]
def rowFactor : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(3075/12044),(3075/12044),(15425/108396)],#v[0,1,(3075/15119),(15425/136071)],#v[0,0,1,(15425/163746)],#v[0,0,0,1]]
def rowGram : GramCertificate 4 4 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 2 :=
  #v[(169581/15625),(47993815061/16958100000)]
def columnFactor : Vector (Vector ℚ 2) 2 :=
  #v[#v[1,(99935/678324)],#v[0,1]]
def columnGram : GramCertificate 2 2 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(59371/25000)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 4).mulVec
      (finiteK4FixedWeight 5 5 4 : Fin (fourRowFiniteSeedFullSize 4) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed5Coefficient 5 5 4) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed5Coefficient 5 4) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed5Coefficient 5 4) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed5Coefficient 4) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M5S4
