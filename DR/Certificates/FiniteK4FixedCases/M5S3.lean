import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 5×5, seed 3.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M5S3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 8 :=
  #v[(227219/125000),(84138906/28402375),(944871080317/673111248000),(579419845678161/236217770079250),(20076628261012207411/11588396913563220000),(3062138974288663751473339/2007662826101220741100000),(9981167024779805643468170539/13779625384298986881630025500),(1191057871434076316990618041340323/1497175053716970846520225580850000)]
def principalFactor : Vector (Vector ℚ 8) 8 :=
  #v[#v[1,(-29000/227219),(-6750/227219),(-35000/227219),(-147460/227219),(-312275/1363314),(-8375/227219),(-300775/1363314)],#v[0,1,(127721611/673111248),(262497829/673111248),(20944969/84138906),(228940673/2019333744),(37882949/336555624),(617455849/2019333744)],#v[0,0,1,(46763001955/944871080317),(-366153758680/944871080317),(-991016937049/2834613240951),(553121321014/944871080317),(-1564560442385/2834613240951)],#v[0,0,0,1,(455073337345855/2317679382712644),(739055219810407/2317679382712644),(375088547884889/2317679382712644),(133686613196455/3476519074068966)],#v[0,0,0,0,1,(-1791309142446128345/20076628261012207411),(-2897046379362374215/20076628261012207411),(-9647839139052883690/60229884783036622233)],#v[0,0,0,0,0,1,(-3359335742427323772216550/9186416922865991254420017),(1424053947257826618441213/3062138974288663751473339)],#v[0,0,0,0,0,0,1,(4415627644113325980817083111/19962334049559611286936341078)],#v[0,0,0,0,0,0,0,1]]
def principalGram : GramCertificate 8 8 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 3 :=
  #v[(7313/1000),(693473099/548475000),(384913548802967/1040209648500000)]
def rowFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(6550/7313),(5498/7313)],#v[0,1,(510183147/1386946198)],#v[0,0,1]]
def rowGram : GramCertificate 3 3 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 3 :=
  #v[(7521/1000),(79265687/62675000),(133922294090813/356695591500000)]
def columnFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(6691/7521),(5647/7521)],#v[0,1,(175483633/475594122)],#v[0,0,1]]
def columnGram : GramCertificate 3 3 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(176783/250000)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 3).mulVec
      (finiteK4FixedWeight 5 5 3 : Fin (fourRowFiniteSeedFullSize 3) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed5Coefficient 5 5 3) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed5Coefficient 5 3) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed5Coefficient 5 3) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed5Coefficient 3) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M5S3
