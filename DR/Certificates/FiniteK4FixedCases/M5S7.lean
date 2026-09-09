import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 5×5, seed 7.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M5S7
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 7 :=
  #v[(677731/93750),(1303090497/677731000),(690439141235383/96525222000000),(25890035181320286713/13981392610016505750),(5406647061188273/768579216375000),(15038390968460265857/8650635297901236800),(13158859679569/7440568456250)]
def principalFactor : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(311625/2710924),(-122625/2710924),(57375/1355462),(-122625/2710924),(57375/1355462),(-203247/2710924)],#v[0,1,(103493791/579151332),(-765633209/5212361988),(103493791/579151332),(-765633209/5212361988),(-355761029/1737453996)],#v[0,0,1,(259260166014625/2071317423706149),(-38918048825625/690439141235383),(107232941364625/2071317423706149),(-47891468745599/690439141235383)],#v[0,0,0,1,(931444119/4099089154),(-3081710711/16396356616),(-949172505/4099089154)],#v[0,0,0,0,1,(3059773240739625/21626588244753092),(-327943553154894/5406647061188273)],#v[0,0,0,0,0,1,(-1662123846/5952454765)],#v[0,0,0,0,0,0,1]]
def principalGram : GramCertificate 7 7 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 2 :=
  #v[(1525523/125000),(243961939981/76276150000)]
def rowFactor : Vector (Vector ℚ 2) 2 :=
  #v[#v[1,(267745/1525523)],#v[0,1]]
def rowGram : GramCertificate 2 2 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 4 :=
  #v[(5401/1000),(3210639/675125),(3228309/726800),(2163841/609000)]
def columnFactor : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(1867/5401),(1867/5401),(1235/5401)],#v[0,1,(1867/7268),(1235/7268)],#v[0,0,1,(247/1827)],#v[0,0,0,1]]
def columnGram : GramCertificate 4 4 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(1183/500)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 7).mulVec
      (finiteK4FixedWeight 5 5 7 : Fin (fourRowFiniteSeedFullSize 7) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed5Coefficient 5 5 7) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed5Coefficient 5 7) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed5Coefficient 5 7) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed5Coefficient 7) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M5S7
