import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 20×20, seed 7.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M20S7
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 7 :=
  #v[(204227021/10000000),(25748244933542527/9700783497500000),(164959642088039222642861/8239438378733608640000),(415825857007015271472409424054217/156711659983637261510717950000000),(17315361521709063285711781/888581090016444450000000),(218150956971233299220281960757191/82247967228118050607130959750000),(253506637483596104353031/186467302951156940000000)]
def principalFactor : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(-168951/204227021),(-28441213/204227021),(1273166/204227021),(-28441213/204227021),(1273166/204227021),(-23187362/612681063)],#v[0,1,(4848984832777537/102992979734170108),(272360178175117/102992979734170108),(4848984832777537/102992979734170108),(272360178175117/102992979734170108),(2803374955166879/51496489867085054)],#v[0,0,1,(104001644990769701941/4123991052200980566071525),(-3343239448142245653591647/20619955261004902830357625),(149047935180256042148341/20619955261004902830357625),(-913910998024283454228482/20619955261004902830357625)],#v[0,0,0,1,(4848984832777537/88858109001644445),(204201633847114/88858109001644445),(15028355901915466/266574327004933335)],#v[0,0,0,0,1,(21002438196602226760627/17315361521709063285711781),(-2770740952774009843920962/51946084565127189857135343)],#v[0,0,0,0,0,1,(6618231036414829/111880381770694164)],#v[0,0,0,0,0,0,1]]
def principalGram : GramCertificate 7 7 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 2 :=
  #v[(1330839667/40000000),(991444435975377119/212934346720000000)]
def rowFactor : Vector (Vector ℚ 2) 2 :=
  #v[#v[1,(513199211/2661679334)],#v[0,1]]
def rowGram : GramCertificate 2 2 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 4 :=
  #v[(440426541/10000000),(24234549881966707/550533176250000),(99081261650565593/2251916980000000),(187240137062834673/78257842670000000)]
def columnFactor : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(9956855/440426541),(9956855/440426541),(-172547/146808847)],#v[0,1,(9956855/450383396),(-517641/450383396)],#v[0,0,1,(-517641/460340251)],#v[0,0,0,1]]
def columnGram : GramCertificate 4 4 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(202771941/10000000)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed20Coefficient 20 20 7).mulVec
      (finiteK4FixedWeight 20 20 7 : Fin (fourRowFiniteSeedFullSize 7) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed20Coefficient 20 20 7) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed20Coefficient 20 7) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed20Coefficient 20 7) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed20Coefficient 7) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M20S7
