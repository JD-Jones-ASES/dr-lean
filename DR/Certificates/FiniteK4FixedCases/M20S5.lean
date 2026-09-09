import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 20×20, seed 5.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M20S5
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 8 :=
  #v[(100218121/5000000),(210095681069127/10021812100000),(368785334702210197800083/70031893689709000000000),(1179200394639393430133496364831729/66381360246397835604014940000000),(311621242519789298266145551534907187101079/5896001973196967150667481824158645000000),(95076262439614055135382538300239785749950244529/30319904677601120912381729338531510096321200000),(2334385813100315974421332638612217091276665947922241880121691/506566326278263685761318164063677578475734902850512000000000),(53720056106109592709300349671081206361827073502085220700236368342247/16977351368002297995791510098997942482012115984889031855430480000000)]
def principalFactor : Vector (Vector ℚ 8) 8 :=
  #v[#v[1,(-33792373/100218121),(-9568085/200436242),(-71251843/200436242),(-441235/100218121),(2996147/200436242),(-22239313/601308726),(11282721/801744968)],#v[0,1,(604632775425389/21009568106912700),(-1803484450732681/5252392026728175),(-40881848144719/4201913621382540),(-12952834510121/21009568106912700),(42735838478713/1800820123449660),(236987159288491/28012757475883600)],#v[0,0,1,(258318221578866069511466/1106356004106630593400249),(188999299165274043424855/1106356004106630593400249),(-42886369413561009661583/3319068012319891780200747),(1033698090730706994159455/3319068012319891780200747),(31475061680375186703931/1475141338808840791200332)],#v[0,0,0,1,(-18068499225978415396954149056257/1179200394639393430133496364831729),(40506998870623018750566458174918/3537601183918180290400489094495187),(186608546513151764349350086174672/3537601183918180290400489094495187),(27376499363951695406552796907749/2358400789278786860266992729663458)],#v[0,0,0,0,1,(829783503655591775093855360263141946783/50533174462668534853969548897552516827202),(107839012475778819310439170293834409570871/7478909820474943158387493236837772490425896),(44562222118383771649281311757747824622329/2492969940158314386129164412279257496808632)],#v[0,0,0,0,0,1,(1078491878726338189107105476047663028706194215913/19015252487922811027076507660047957149990048905800),(1012400799048450241442797091188709238405427555341/19015252487922811027076507660047957149990048905800)],#v[0,0,0,0,0,0,1,(-4510462997444465853234042801178286826674368099925524214083/212216892100028724947393876237474281025151449811112898192881)],#v[0,0,0,0,0,0,0,1]]
def principalGram : GramCertificate 8 8 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 3 :=
  #v[(2772588353/60000000),(9328369740465556781/221807068240000000),(7900751982409317754471803427/3358213106567600441160000000)]
def rowFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(911387841/5545176706),(183480693/5545176706)],#v[0,1,(284421436753720939/9328369740465556781)],#v[0,0,1]]
def rowGram : GramCertificate 3 3 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 3 :=
  #v[(125546109/2500000),(7545821217695689/156932636250000),(285530734119026630525931211/86927860427854337280000000)]
def columnFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(45908761/251092218),(10983389/251092218)],#v[0,1,(10463835959253643/241466278966262048)],#v[0,0,1]]
def columnGram : GramCertificate 3 3 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(1012521503/20000000)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed20Coefficient 20 20 5).mulVec
      (finiteK4FixedWeight 20 20 5 : Fin (fourRowFiniteSeedFullSize 5) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed20Coefficient 20 20 5) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed20Coefficient 20 5) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed20Coefficient 20 5) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed20Coefficient 5) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M20S5
