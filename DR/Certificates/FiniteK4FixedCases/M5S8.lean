import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 5×5, seed 8.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M5S8
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 11 :=
  #v[(97107/12500),(284601727/38842800),(983406486363/284601727000),(90368825040412981/12292581079537500),(3599072308291020345/1445901200646607696),(847644297668179348373/719814461658204069000),(1288938078350557/239488862661000),(15172194962784580347/6444690391752785000),(485439519862250536063/344822612790558644250),(23227348678369264468635859/40048760388635669225197500),(19902514328702595238376341094611/18581878942695411574908687200000)]
def principalFactor : Vector (Vector ℚ 11) 11 :=
  #v[#v[1,(123925/194214),(109075/194214),(-3550/97107),(-4425/32369),(-6025/32369),(62275/388428),(-10925/194214),(-10125/129476),(-16025/194214),(-189481/776856)],#v[0,1,(86271259/284601727),(-171060568/1423008635),(28846452/284601727),(-154684824/284601727),(176755357/569203454),(781875083/1423008635),(735929871/2846017270),(-250922089/1423008635),(1668725101/5692034540)],#v[0,0,1,(-290153539484/983406486363),(-1290291671420/983406486363),(-236186607782/421459922727),(-1391248122905/1966812972726),(-615571843424/983406486363),(-2483665080209/5900438918178),(110038443629/983406486363),(-1265873602727/3933625945452)],#v[0,0,0,1,(90222417386312675/180737650080825962),(240449294933604575/542212950242477886),(41469409763860475/361475300161651924),(-14928026056528105/180737650080825962),(-122595428285777005/1084425900484955772),(-17348911778861585/180737650080825962),(-200019725515903513/722950600323303848)],#v[0,0,0,0,1,(2513178223745086211/5998453847151700575),(-8940076537933374617/35990723082910203450),(26909117793814400917/89976807707275508625),(-18909814002807977891/179953615414551017250),(-5769997433490544039/17995361541455101725),(2689621675513613903/359907230829102034500)],#v[0,0,0,0,0,1,(-48412576521/53219747258),(-37959717204/133049368145),(-144980145583/266098736290),(-7288173447/26609873629),(-198476451411/532197472580)],#v[0,0,0,0,0,0,1,(635338259577946/1288938078350557),(712707657166751/1288938078350557),(-100160655831362/1288938078350557),(-369375961516999/1288938078350557)],#v[0,0,0,0,0,0,0,1,(222057086006559787/1379290451162234577),(-1138222098143933237/15172194962784580347),(1698248530787725921/15172194962784580347)],#v[0,0,0,0,0,0,0,0,1,(-286184355711596566615/970879039724501072126),(528175645658594376605/3883516158898004288504)],#v[0,0,0,0,0,0,0,0,0,1,(-113091077719496178886399/185818789426954115749086872)],#v[0,0,0,0,0,0,0,0,0,0,1]]
def principalGram : GramCertificate 11 11 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 3 :=
  #v[(3763/250),(7401223/3763000),(72917583211057/166527517500000)]
def rowFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(5925/7526),(2797/3763)],#v[0,1,(147034399/370061150)],#v[0,0,1]]
def rowGram : GramCertificate 3 3 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 4 :=
  #v[(13083/1000),(39259/33375),(30597761/12782000),(1340897687153/2294832075000)]
def columnFactor : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(1783/1869),(12659/13083),(3813/4361)],#v[0,1,(12659/25564),(11439/25564)],#v[0,0,1,(19761949/30597761)],#v[0,0,0,1]]
def columnGram : GramCertificate 4 4 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(21001/18750)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 8).mulVec
      (finiteK4FixedWeight 5 5 8 : Fin (fourRowFiniteSeedFullSize 8) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed5Coefficient 5 5 8) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed5Coefficient 5 8) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed5Coefficient 5 8) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed5Coefficient 8) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M5S8
