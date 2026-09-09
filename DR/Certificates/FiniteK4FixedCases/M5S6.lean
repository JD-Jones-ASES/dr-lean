import DR.Certificates.FiniteK4FixedBlocks
import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.StrictGram

/-! Generated exact fixed-board block data and kernel checks for 5×5, seed 6.
No numerical PSD test is a premise. -/
namespace DittertRybin.Certificates.FiniteK4FixedCases.M5S6
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

def principalWeights : Vector ℚ 11 :=
  #v[(390759/50000),(152228193581/19537950000),(1688208111/184604500),(2204248618973/1688208111000),(2485650478224174700497/454415771920069328500),(560140463183292050181372/103568769926007279187375),(306788675260093021/134721363693109800),(55346458493531138821561/30678867526009302100000),(263964118258506711474794699731853977/345176778718729728228721670982810000),(61065164174486684164248429103762562563/98986544346940016803048012399445241375),(15152159400573575606074930137833/13340477355040613843534240850000)]
def principalFactor : Vector (Vector ℚ 11) 11 :=
  #v[#v[1,(-21550/390759),(53750/390759),(-11350/130253),(250750/390759),(-19350/130253),(-27500/390759),(-187481/781518),(222050/390759),(-75200/390759),(-29719/390759)],#v[0,1,(53750/369209),(-34050/369209),(-17279897450/152228193581),(96731841750/152228193581),(-27500/369209),(-187481/738418),(-24599899300/152228193581),(85147475950/152228193581),(-29719/369209)],#v[0,0,1,(-85973638/1688208111),(446914369/1688208111),(446914369/1688208111),(2130018281/3376416222),(225171451/3376416222),(-327778741/1688208111),(-327778741/1688208111),(2007042817/3376416222)],#v[0,0,0,1,(-1919965026560/2204248618973),(-1919965026560/2204248618973),(-1674107462882/2204248618973),(-878702750375/4408497237946),(-355469664775/2204248618973),(-355469664775/2204248618973),(-855576635482/2204248618973)],#v[0,0,0,0,1,(-87925749502159453123/828550159408058233499),(673016214464719924069/2485650478224174700497),(230900745605037839912/828550159408058233499),(718863457766429754549/1657100318816116466998),(-3021454913989581136903/4971300956448349400994),(-42389594948410945816/2485650478224174700497)],#v[0,0,0,0,0,1,(1632310268426641/5388854547724392),(70002336113521/224535606155183),(-79559818503059123431709/140035115795823012545343),(104610943853244574773607/280070231591646025090686),(-12851282335703/673606818465549)],#v[0,0,0,0,0,0,1,(271914121572317127/3067886752600930210),(30456407609487184/1533943376300465105),(30456407609487184/1533943376300465105),(21849666479513209/180463926623584130)],#v[0,0,0,0,0,0,0,1,(-15314605620708477235320/55346458493531138821561),(-15314605620708477235320/55346458493531138821561),(13540563528367894779473/55346458493531138821561)],#v[0,0,0,0,0,0,0,0,1,(-116053082524815930872348569935325393/263964118258506711474794699731853977),(-27050560042155658282919176545508722/263964118258506711474794699731853977)],#v[0,0,0,0,0,0,0,0,0,1,(-65060258579267343246924123/355746062801083035827579756)],#v[0,0,0,0,0,0,0,0,0,0,1]]
def principalGram : GramCertificate 11 11 :=
  ⟨principalWeights.get, fun i j => (principalFactor.get i).get j⟩

def rowWeights : Vector ℚ 4 :=
  #v[(2629/200),(15489261/13145000),(1542230459/642175000),(135209986596451/231334568850000)]
def rowFactor : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(12542/13145),(12792/13145),(11538/13145)],#v[0,1,(12792/25687),(11538/25687)],#v[0,0,1,(998058876/1542230459)],#v[0,0,0,1]]
def rowGram : GramCertificate 4 4 :=
  ⟨rowWeights.get, fun i j => (rowFactor.get i).get j⟩

def columnWeights : Vector ℚ 3 :=
  #v[(7421/500),(5790323/2968400),(143398915212719/325705668750000)]
def columnFactor : Vector (Vector ℚ 3) 3 :=
  #v[#v[1,(11709/14842),(11083/14842)],#v[0,1,(283842908/723790375)],#v[0,0,1]]
def columnGram : GramCertificate 3 3 :=
  ⟨columnWeights.get, fun i j => (columnFactor.get i).get j⟩

def interactionWeights : Vector ℚ 1 :=
  #v[(83779/75000)]
def interactionFactor : Vector (Vector ℚ 1) 1 :=
  #v[#v[1]]
def interactionGram : GramCertificate 1 1 :=
  ⟨interactionWeights.get, fun i j => (interactionFactor.get i).get j⟩

theorem full_kernel :
    (finiteK4FixedFullMatrix finiteK4Fixed5Coefficient 5 5 6).mulVec
      (finiteK4FixedWeight 5 5 6 : Fin (fourRowFiniteSeedFullSize 6) → ℚ) = 0 := by
  ext i
  fin_cases i <;> decide +kernel

theorem principal_valid : principalGram.StrictValid (finiteK4FixedPrincipalMatrix finiteK4Fixed5Coefficient 5 5 6) := by
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

theorem row_valid : rowGram.StrictValid (finiteK4FixedRowMatrix finiteK4Fixed5Coefficient 5 6) := by
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

theorem column_valid : columnGram.StrictValid (finiteK4FixedColumnMatrix finiteK4Fixed5Coefficient 5 6) := by
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

theorem interaction_valid : interactionGram.StrictValid (finiteK4FixedInteractionMatrix finiteK4Fixed5Coefficient 6) := by
  decide +kernel

end DittertRybin.Certificates.FiniteK4FixedCases.M5S6
