import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 5×5, seed 5.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M5S5
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 8 :=
  #v[(99137/12500),(159611647/24784250),(2222195371973/957669882000),(52892421366301423/8888781487892000),(193312137719112213427/26446210683150711500),(2597086573554027808054477/1159872826314673280562000),(1561750511582845815118404378837/1623179108471267380034048125000),(1000184514108839178056486710235280313/488047034869639317224501368386562500)]
def principalFactor : Vector (Vector ℚ 8) 8 :=
  #v[#v[1,(10200/99137),(61375/198274),(12550/99137),(-12455/396548),(8745/198274),(87785/297411),(1886/99137)],#v[0,1,(45871193/319223294),(-84692687/638446588),(31169401/159611647),(-63249163/159611647),(-40631673/638446588),(17261642/159611647)],#v[0,0,1,(-113986593213/2222195371973),(-4151707006107/4444390743946),(-464375290211/2222195371973),(-751515158117/2222195371973),(-795618149124/2222195371973)],#v[0,0,0,1,(8028147885673437/52892421366301423),(2304973556739010/52892421366301423),(23253958819846991/158677264098904269),(-692844530238580/1706207140848433)],#v[0,0,0,0,1,(158889839008719503271/386624275438224426854),(-11273113372971553812137/28996820657866832014050),(345177363730467362251/966560688595561067135)],#v[0,0,0,0,0,1,(4590342956251366537077323/64927164338850695201361925),(10392286820489266876961718/64927164338850695201361925)],#v[0,0,0,0,0,0,1,(342229955439490981438006621468/1561750511582845815118404378837)],#v[0,0,0,0,0,0,0,1]]
def principalGram : GramCertificate 8 8 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 3 :=
  #v[(390973/37500),(121523448477/78194600000),(2853997941836911/3038086211925000)]
def rowFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(1477263/1563892),(666519/781946)],#v[0,1,(54953212934/121523448477)],#v[0,0,1]]
def rowGram : GramCertificate 3 3 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 3 :=
  #v[(11029/1000),(17180813/11029000),(5104146068167/5369004062500)]
def columnFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(10523/11029),(9433/11029)],#v[0,1,(197887017/429520325)],#v[0,0,1]]
def columnGram : GramCertificate 3 3 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(16671/25000)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 5).mulVec
      (finiteK4FixedWeight 5 5 5 : Fin (fourRowFiniteSeedFullSize 5) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed5Coefficient 5 5 5) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed5Coefficient 5 5) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed5Coefficient 5 5) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed5Coefficient 5) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M5S5
