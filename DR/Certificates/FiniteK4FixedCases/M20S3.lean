import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 20×20, seed 3.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M20S3
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 8 :=
  #v[(92019437/20000000),(5205499725171213/230048592500000),(260108233534235039168201/208219989006848520000000),(1049280892656604653572124793204297/46819482036162307050276180000000),(482241136506643492668832719171505649350503/83942471412528372285769983456343760000000),(64423640335785380557532015519667502445363255021851/38579290920531479413506617533720451948040240000000),(226517516137403123593741683469224536790302399134150310729/177493702965939313780955552962349241431102845468365000000),(112504434682858689976119346451287909889945286312957844602103303787/66596149744396518336560054939952013816348905345440191354326000000)]
def principalFactor : Vector (Vector ℚ 8) 8 :=
  #v[#v[1,(-29351480/92019437),(-6768592/92019437),(-31984002/92019437),(-114340329/184038874),(-22051835/276058311),(-6689602/92019437),(-6982753/92019437)],#v[0,1,(131619039408451/6940666300228284),(1201939248307321/20821998900684852),(-1889533852135279/20821998900684852),(115646492127964/15616499175513639),(6061103978846/578388858352357),(155814706431533/6940666300228284)],#v[0,0,1,(35089539211454379145311/260108233534235039168201),(-51508179425547322661037/260108233534235039168201),(-17386801526185528172222/260108233534235039168201),(9815482357080627846348/260108233534235039168201),(2811721115324970740259/37158319076319291309743)],#v[0,0,0,1,(-85205906278688629947978559793278/1049280892656604653572124793204297),(79133195349645732512435070211231/3147842677969813960716374379612891),(20810264146682292680106569004576/1049280892656604653572124793204297),(9350339657826651524329363816119/1049280892656604653572124793204297)],#v[0,0,0,0,1,(-76990068226372284719906515257729939547826/1446723409519930478006498157514516948051509),(-18568210087876437753663647761597040533652/482241136506643492668832719171505649350503),(-22498907077688845303421196719299682870950/482241136506643492668832719171505649350503)],#v[0,0,0,0,0,1,(1559529397840715690700076634724034691442305346176/27610131572479448810370863794143215333727109295079),(4792764737524025266454226053760162767800420323802/193270921007356141672596046559002507336089765065553)],#v[0,0,0,0,0,0,1,(-507609612200140080311086939096990019085540608712278989277/6342490451847287460624767137138287030128467175756208700412)],#v[0,0,0,0,0,0,0,1]]
def principalGram : GramCertificate 8 8 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 3 :=
  #v[(8707037/500000),(13361331301515997/870703700000000),(181698860755848721739822489/115441902445098214080000000)]
def rowFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(35943189/174140740),(11134609/87070370)],#v[0,1,(2420365755317761/53445325206063988)],#v[0,0,1]]
def rowGram : GramCertificate 3 3 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 3 :=
  #v[(177976597/10000000),(340917726381292429/21357191640000000),(2644420468974396263211342997/1472764577967183293280000000)]
def columnFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(30569349/177976597),(24782380/177976597)],#v[0,1,(32417968788543171/681835452762584858)],#v[0,0,1]]
def columnGram : GramCertificate 3 3 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(1792642691/120000000)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed20Coefficient 20 20 3).mulVec
      (finiteK4FixedWeight 20 20 3 : Fin (fourRowFiniteSeedFullSize 3) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed20Coefficient 20 20 3) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed20Coefficient 20 3) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed20Coefficient 20 3) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed20Coefficient 3) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M20S3
