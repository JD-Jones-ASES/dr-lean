import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 20×20, seed 4.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M20S4
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 7 :=
  #v[(207038753/10000000),(5238879338322161/258798441250000),(17281102788042317/880758460000000),(397285831578641743/296339847240000000),(72293960676730694122949953778583/33758769596076872042019215000000),(199951290776715881967622093250738440834843044403/93374682681316481114791369384743709939908000000),(2921111044938522033018147530124114184703/1364186070887697967354009032433061500000)]
def principalFactor : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(-30887061/207038753),(-30887061/207038753),(-43601681/1242232518),(-404185/207038753),(1032656/207038753),(1032656/207038753)],#v[0,1,(-30887061/176151692),(-43601681/1056910152),(28759389109669/5987290672368184),(-7398035645327/5987290672368184),(258164/44037923)],#v[0,0,1,(-43601681/871587786),(28759389109669/4937457939440662),(28759389109669/4937457939440662),(-529032421642/2468728969720331)],#v[0,0,0,1,(43518049904184276/397285831578641743),(43518049904184276/397285831578641743),(43518049904184276/397285831578641743)],#v[0,0,0,0,1,(-989387575808970629688430458949/144587921353461388245899907557166),(-989387575808970629688430458949/144587921353461388245899907557166)],#v[0,0,0,0,0,1,(-989387575808970629688430458949/143598533777652417616211477098217)],#v[0,0,0,0,0,0,1]]
def principalGram : GramCertificate 7 7 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 4 :=
  #v[(771151309/20000000),(118900376151953601/3084605236000000),(604456507647368163/15685674700000000),(11012161398560091/5316107740000000)]
def rowFactor : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(13132426/771151309),(13132426/771151309),(-1225036/771151309)],#v[0,1,(13132426/784283735),(-1225036/784283735)],#v[0,0,1,(-1225036/797416161)],#v[0,0,0,1]]
def rowGram : GramCertificate 4 4 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 2 :=
  #v[(258086651/8000000),(14879596864714677989/3922917095200000000)]
def columnFactor : Vector (Vector ℚ 2) 2 :=
  #v[#v[1,(453799167/2580866510)],#v[0,1]]
def columnGram : GramCertificate 2 2 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(397778101/20000000)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed20Coefficient 20 20 4).mulVec
      (finiteK4FixedWeight 20 20 4 : Fin (fourRowFiniteSeedFullSize 4) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed20Coefficient 20 20 4) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed20Coefficient 20 4) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed20Coefficient 20 4) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed20Coefficient 4) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M20S4
