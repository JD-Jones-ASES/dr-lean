import DR.Certificates.FiniteK3EnvelopeSparseEquations

/-! Exact mathematical rational data and kernel checks for K3 on 4x6.
Reproduce with scripts/generate_finite_k3_envelope.py --case 4 6 --check. -/
namespace DittertRybin.Certificates.FiniteK3Cases.C4N6
open scoped BigOperators

def numerators : Vector ℤ 93 :=
  #v[1300,154,185,-175,4316,-654,-57,1707,-567,5160,456,-545,-625,5016,-57,51,-420,4892,-416,-3,675,1629,-948,6120,-1000,294,1782,-1136,10872,-3144,-228,5538,-4398,-1572,5778,1140,768,-78,4830,612,-1260,90,100,-728,7128,126,2322,-1782,-90,3438,-1278,5490,270,-1000,-1028,7218,-504,4056,-924,5550,900,-252,1818,-1116,-216,-198,-630,-453,13140,1152,8622,774,-342,-414,-3834,8334,-864,5490,-2070,270,-1566,3672,-1872,7902,3006,2142,-972,-3528,-2052,7452,1566,3132,-1000]
def denominator : Nat := 1800
def coeff (i : Fin 93) : ℚ := (numerators.get i:ℚ)/denominator

def h0Weights : Vector ℚ 4 :=
  #v[(497/180),(3340289/1491000),(183350583/83507225),(1838412329/860576400)]
def h0Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(1137/2485),(1137/2485),(1137/2485)],
    #v[0,1,(-471701/3340289),(-471701/3340289)],
    #v[0,0,1,(-471701/2868588)],
    #v[0,0,0,1]]
def h0Gram : GramCertificate 4 4 :=
  ⟨fun i => h0Weights.get i,fun i j => (h0Factors.get i).get j⟩

def b0Weights : Vector ℚ 7 :=
  #v[(13/18),(266951/93600),(135346561/48051180),(236795153/85407120),(5483639/31129950),(1538309/3850875),(1538309/5134500)]
def b0Factors : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(37/260),(37/260),(37/260),(77/650),(-7/52),(-7/52)],
    #v[0,1,(-29709/266951),(-29709/266951),(-20518/1334755),(1471/15703),(-31205/266951)],
    #v[0,0,1,(-29709/237242),(-10259/593105),(-72954548/676732805),(55274753/676732805)],
    #v[0,0,0,1,(-20518/1037665),(-145909096/1183975765),(-145909096/1183975765)],
    #v[0,0,0,0,1,(-1/3),(-1/3)],
    #v[0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,1]]
def b0Gram : GramCertificate 7 7 :=
  ⟨fun i => b0Weights.get i,fun i j => (b0Factors.get i).get j⟩

def h1Weights : Vector ℚ 4 :=
  #v[(178/45),(6126959/3204000),(869656964/459521925),(128542401/68801975)]
def h1Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(1459/3560),(1459/3560),(1459/3560)],
    #v[0,1,(-622801/6126959),(-622801/6126959)],
    #v[0,0,1,(-622801/5504158)],
    #v[0,0,0,1]]
def h1Gram : GramCertificate 4 4 :=
  ⟨fun i => h1Weights.get i,fun i j => (h1Factors.get i).get j⟩

def b1Weights : Vector ℚ 11 :=
  #v[(1223/450),(494971/183450),(1121195419/197988400),(42940793812/8698929975),(48305972222299/12882238143600),(26240123655710952/7004365972233355),(10814626836029/3162985011537),(920758348469457/270365670900725),(15565699/40098000),(148013/247050),(148013/329400)]
def b1Factors : Vector (Vector ℚ 11) 11 :=
  #v[#v[1,(-104/1223),(675/4892),(1629/4892),(675/4892),(1629/4892),(675/4892),(1629/4892),(-3/4892),(-237/1223),(-237/1223)],
    #v[0,1,(687489/1979884),(331647/1979884),(687489/1979884),(331647/1979884),(687489/1979884),(331647/1979884),(-1/1492),(-79/373),(-79/373)],
    #v[0,0,1,(-41546341/115985733),(1603469381/3363586257),(-1618639645/3363586257),(1603469381/3363586257),(-1618639645/3363586257),(97523884/3363586257),(85787896/3363586257),(-357706120/3363586257)],
    #v[0,0,0,1,(-30587857673/85881587624),(29984336671/85881587624),(-30587857673/85881587624),(29984336671/85881587624),(18373/406696),(8081/203348),(-33695/203348)],
    #v[0,0,0,0,1,(-1488313646821/48305972222299),(10131606523431/48305972222299),(-10462939553529/48305972222299),(2130014612313/48305972222299),(-704095306306/4391452020209),(1806095092298/48305972222299)],
    #v[0,0,0,0,0,1,(-887047872517/4217313348716),(857201544161/4217313348716),(18373/403838),(-18338507/110853531),(4276421/110853531)],
    #v[0,0,0,0,0,0,1,(3399850674296/54073134180145),(52668519663357/1081462683602900),(-95755266179287/540731341801450),(-95755266179287/540731341801450)],
    #v[0,0,0,0,0,0,0,1,(18373/400980),(-18338507/110069010),(-18338507/110069010)],
    #v[0,0,0,0,0,0,0,0,1,(-1/3),(-1/3)],
    #v[0,0,0,0,0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,0,0,0,0,1]]
def b1Gram : GramCertificate 11 11 :=
  ⟨fun i => b1Weights.get i,fun i j => (b1Factors.get i).get j⟩

def h2Weights : Vector ℚ 4 :=
  #v[(389/100),(99337/38900),(25481/12340),(220484677/114664500)]
def h2Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(228/389),(262/389),(262/389)],
    #v[0,1,(262/617),(262/617)],
    #v[0,0,1,(100246/382215)],
    #v[0,0,0,1]]
def h2Gram : GramCertificate 4 4 :=
  ⟨fun i => h2Weights.get i,fun i j => (h2Factors.get i).get j⟩

def b2Weights : Vector ℚ 7 :=
  #v[(161/60),(3451/1380),(195793/64260),(103770557/35242740),(88895773/111925100),(35140766/88895773),(443/2250)]
def b2Factors : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(-6/23),(10/483),(10/483),(102/805),(3/161),(-52/345)],
    #v[0,1,(10/357),(10/357),(33/595),(12/85),(-52/255)],
    #v[0,0,1,(-35900/195793),(-3915/195793),(-3915/195793),(11095/195793)],
    #v[0,0,0,1,(-3915/159893),(-3915/159893),(-140318/799465)],
    #v[0,0,0,0,1,(-63002577/88895773),(-12946598/88895773)],
    #v[0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,1]]
def b2Gram : GramCertificate 7 7 :=
  ⟨fun i => b2Weights.get i,fun i j => (b2Factors.get i).get j⟩

def h3Weights : Vector ℚ 4 :=
  #v[(511/100),(12103/7300),(2341/1900),(893663/758484)]
def h3Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(60/73),(44/73),(44/73)],
    #v[0,1,(44/133),(44/133)],
    #v[0,0,1,(4406/21069)],
    #v[0,0,0,1]]
def h3Gram : GramCertificate 4 4 :=
  ⟨fun i => h3Weights.get i,fun i j => (h3Factors.get i).get j⟩

def b3Weights : Vector ℚ 11 :=
  #v[(37/12),(2671/370),(53479617/13355000),(6212107244/2228317375),(673598426423/155302681100),(62660577056292/16839960660575),(21385684710160693/6266057705629200),(23086406358750696/8225263350061805),(112051810204587637/388369452764030400),(1169602231429636099/4482072408183505480),(25727/128400)]
def b3Factors : Vector (Vector ℚ 11) 11 :=
  #v[#v[1,(6/37),(303/925),(-186/925),(-33/925),(-21/185),(-33/925),(-21/185),(-42/925),(-36/925),(-151/1850)],
    #v[0,1,(17117/26710),(4109/26710),(-637/26710),(-641/26710),(-637/26710),(-641/26710),(1226/13355),(1663/26710),(-773/2671)],
    #v[0,0,1,(-114769/53479617),(-372329/17826539),(158795/17826539),(-372329/17826539),(158795/17826539),(683362/53479617),(5225461/53479617),(-9464867/53479617)],
    #v[0,0,0,1,(-385291015/3106053622),(-171191059/3106053622),(-385291015/3106053622),(-171191059/3106053622),(-6684686795/74545286928),(-6215234483/74545286928),(3473/550032)],
    #v[0,0,0,0,1,(253930335791/673598426423),(-92043791400/673598426423),(-23832184354/51815263571),(121945554061/4041590558538),(-823932375635/4041590558538),(1042309221017/4041590558538)],
    #v[0,0,0,0,0,1,(-59664286623293/125321154112584),(5367497945381/125321154112584),(-5240351213293/20886859018764),(2605698004939/20886859018764),(7690673/41062596)],
    #v[0,0,0,0,0,0,1,(693287976606071/1645052670012361),(-1852915121971296/21385684710160693),(-4912874317081776/21385684710160693),(-4554078117798060/21385684710160693)],
    #v[0,0,0,0,0,0,0,1,(-152072838700997/647282421273384),(8006951101819/647282421273384),(-746092195/4980158352)],
    #v[0,0,0,0,0,0,0,0,1,(-34636161822970727/112051810204587637),(-38707824190808455/112051810204587637)],
    #v[0,0,0,0,0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,0,0,0,0,1]]
def b3Gram : GramCertificate 11 11 :=
  ⟨fun i => b3Weights.get i,fun i j => (b3Factors.get i).get j⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem sparse_equations_checked : FiniteK3EnvelopeSparseIntegerEquations denominator (numerators.get 0) numerators.get := by
  decide +kernel

private theorem integer_equations_checked : FiniteK3EnvelopeIntegerEquations denominator (numerators.get 0) numerators.get :=
  finiteK3EnvelopeIntegerEquations_of_sparse _ _ _ sparse_equations_checked

private theorem equations_checked : FiniteK3EnvelopeEquations 4 6 coeff := by
  exact finiteK3EnvelopeEquations_of_integer 4 6 denominator (numerators.get 0) numerators.get
    (by decide) (by decide +kernel) integer_equations_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h0_checked : h0Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 0) := by
  change h0Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 0) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b0_checked : b0Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 6 (by decide) 0) := by
  change b0Gram.StrictValid (Matrix.of (fun i j : Fin 7 => (finiteK3EnvelopeTableB0 coeff 4 6 (by decide) 0) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h1_checked : h1Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 1) := by
  change h1Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 1) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b1_checked : b1Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 6 (by decide) 1) := by
  change b1Gram.StrictValid (Matrix.of (fun i j : Fin 11 => (finiteK3EnvelopeTableB0 coeff 4 6 (by decide) 1) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h2_checked : h2Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 2) := by
  change h2Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 2) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b2_checked : b2Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 6 (by decide) 2) := by
  change b2Gram.StrictValid (Matrix.of (fun i j : Fin 7 => (finiteK3EnvelopeTableB0 coeff 4 6 (by decide) 2) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h3_checked : h3Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 3) := by
  change h3Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 3) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b3_checked : b3Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 6 (by decide) 3) := by
  change b3Gram.StrictValid (Matrix.of (fun i j : Fin 11 => (finiteK3EnvelopeTableB0 coeff 4 6 (by decide) 3) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem kernels_checked : ∀ s : Fin 4,∀ i,
    (∑ j,finiteK3EnvelopeFlatTableB coeff 4 6 (by decide) s i j*
      finiteK3EnvelopeKernel 4 6 s j)=0 := by
  decide +kernel

theorem valid : FiniteK3EnvelopeValid 4 6 (by decide) coeff := by
  refine ⟨equations_checked,?_⟩
  intro s
  have hk := kernels_checked s
  rw [← finiteK3EnvelopeFlatB_eq_table coeff 4 6 (by decide) (by decide) s] at hk
  fin_cases s
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h0Gram.strictValid_posDef _ h0_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 6 (by decide) (by decide)]
      exact b0Gram.strictValid_posDef _ b0_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h1Gram.strictValid_posDef _ h1_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 6 (by decide) (by decide)]
      exact b1Gram.strictValid_posDef _ b1_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h2Gram.strictValid_posDef _ h2_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 6 (by decide) (by decide)]
      exact b2Gram.strictValid_posDef _ b2_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h3Gram.strictValid_posDef _ h3_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 6 (by decide) (by decide)]
      exact b3Gram.strictValid_posDef _ b3_checked

end DittertRybin.Certificates.FiniteK3Cases.C4N6
