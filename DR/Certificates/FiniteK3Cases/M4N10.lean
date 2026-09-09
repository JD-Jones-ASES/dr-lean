import DR.Certificates.FiniteK3EnvelopeSparseEquations

/-! Exact mathematical rational data and kernel checks for K3 on 4x10.
Reproduce with scripts/generate_finite_k3_envelope.py --case 4 10 --check. -/
namespace DittertRybin.Certificates.FiniteK3Cases.C4N10
open scoped BigOperators

def numerators : Vector ℤ 93 :=
  #v[1650,-115,218,-47,6948,-502,93,2312,-418,6390,669,-289,-716,7072,520,-199,-562,6830,-1998,-136,-571,3459,-517,9348,-700,639,3532,-886,15206,-1170,-530,6058,-2108,-1606,6752,400,1378,-80,6164,-82,-1440,326,194,-406,10078,-318,1366,-636,-34,3398,-674,7602,110,-700,-852,9366,-434,4752,-638,6694,-910,-520,1302,-2122,2,-686,-292,71,20920,1654,9704,1018,442,850,-3436,10710,-514,7460,-1250,624,-1286,5536,-1266,11416,2228,1356,-548,-3426,-1942,8640,944,4206,-700]
def denominator : Nat := 2000
def coeff (i : Fin 93) : ℚ := (numerators.get i:ℚ)/denominator

def h0Weights : Vector ℚ 4 :=
  #v[(149/40),(82719/29800),(503522599/183820000),(82165164/30509125)]
def h0Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(273/745),(273/745),(273/745)],
    #v[0,1,(-31657/275730),(-31657/275730)],
    #v[0,0,1,(-31657/244073)],
    #v[0,0,0,1]]
def h0Gram : GramCertificate 4 4 :=
  ⟨fun i => h0Weights.get i,fun i j => (h0Factors.get i).get j⟩

def b0Weights : Vector ℚ 7 :=
  #v[(33/40),(1311997/412500),(33300164879/10495976000),(15774508953/4985801000),(163557313/1049692000),(3713017/7513875),(3713017/10018500)]
def b0Factors : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(109/825),(109/825),(109/825),(-23/330),(-47/1650),(-47/1650)],
    #v[0,1,(-262187/5247988),(-262187/5247988),(22315/1311997),(139262/1311997),(-585577/5247988)],
    #v[0,0,1,(-262187/4985801),(89260/4985801),(-3547939788/33300164879),(3357394597/33300164879)],
    #v[0,0,0,1,(44630/2361807),(-197107766/1752723217),(-197107766/1752723217)],
    #v[0,0,0,0,1,(-1/3),(-1/3)],
    #v[0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,1]]
def b0Gram : GramCertificate 7 7 :=
  ⟨fun i => b0Weights.get i,fun i j => (b0Factors.get i).get j⟩

def h1Weights : Vector ℚ 4 :=
  #v[(628/125),(11076543/5024000),(12062924513/5538271500),(21147397331/9859358000)]
def h1Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(2209/5024),(2209/5024),(2209/5024)],
    #v[0,1,(-1217185/11076543),(-1217185/11076543)],
    #v[0,0,1,(-1217185/9859358)],
    #v[0,0,0,1]]
def h1Gram : GramCertificate 4 4 :=
  ⟨fun i => h1Weights.get i,fun i j => (h1Factors.get i).get j⟩

def b1Weights : Vector ℚ 11 :=
  #v[(683/200),(1333028/426875),(1789336203/266605600),(9938849766993/1491113502500),(117731520146997347/19877699533986000),(17432002712675637336/2943288003674933675),(37604703851044091/6736512844659200),(20955382003848526221/3760470385104409100),(152915681/843470000),(17391677/60516000),(17391677/80688000)]
def b1Factors : Vector (Vector ℚ 11) 11 :=
  #v[#v[1,(-999/3415),(-571/6830),(3459/6830),(-571/6830),(3459/6830),(-571/6830),(3459/6830),(-68/3415),(-517/6830),(-517/6830)],
    #v[0,1,(1405257/2666056),(188197/2666056),(1405257/2666056),(188197/2666056),(1405257/2666056),(188197/2666056),(-17/604),(-517/4832),(-517/4832)],
    #v[0,0,1,(-247321433/2982227005),(2849410943/8946681015),(-1367154431/8946681015),(2849410943/8946681015),(-1367154431/8946681015),(480079882/8946681015),(-294596981/17893362030),(-576311703/5964454010)],
    #v[0,0,0,1,(-2529912699887/19877699533986),(6120999461039/19877699533986),(-2529912699887/19877699533986),(6120999461039/19877699533986),(108763/1858794),(-19069/1062168),(-261129/2478392)],
    #v[0,0,0,0,1,(621569139383587/117731520146997347),(26810922478545383/117731520146997347),(-8701071942055847/117731520146997347),(5865499553019021/117731520146997347),(-49975438313549133/470926080587989388),(529389793587843/470926080587989388)],
    #v[0,0,0,0,0,1,(-2529912699887/33682564223296),(7683865228271/33682564223296),(108763/2194602),(-519253273/4918834616),(16501349/14756503848)],
    #v[0,0,0,0,0,0,1,(1565806944700357/37604703851044091),(8418205479897632/188023519255220455),(-17931273579880584/188023519255220455),(-17931273579880584/188023519255220455)],
    #v[0,0,0,0,0,0,0,1,(108763/2530410),(-519253273/5671492280),(-519253273/5671492280)],
    #v[0,0,0,0,0,0,0,0,1,(-1/3),(-1/3)],
    #v[0,0,0,0,0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,0,0,0,0,1]]
def b1Gram : GramCertificate 11 11 :=
  ⟨fun i => b1Weights.get i,fun i j => (b1Factors.get i).get j⟩

def h2Weights : Vector ℚ 4 :=
  #v[(2599/500),(26017203/5198000),(5521127/1549750),(13450597461/4416901600)]
def h2Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(1001/5198),(1018/2599),(1018/2599)],
    #v[0,1,(2036/6199),(2036/6199)],
    #v[0,0,1,(8415713/22084508)],
    #v[0,0,0,1]]
def h2Gram : GramCertificate 4 4 :=
  ⟨fun i => h2Weights.get i,fun i j => (h2Factors.get i).get j⟩

def b2Weights : Vector ℚ 7 :=
  #v[(1541/500),(2245081/770500),(1119893/295250),(16839830763/4479572000),(1579610196811/3856000756500),(182044941450394/592353823804125),(302259/2075500)]
def b2Factors : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(-360/1541),(97/3082),(97/3082),(-41/3082),(163/3082),(-203/3082)],
    #v[0,1,(97/2362),(97/2362),(236423/4490162),(-4501/4490162),(-203/2362)],
    #v[0,0,1,(-422759/4479572),(-12997/2239786),(-12997/2239786),(42323/2239786)],
    #v[0,0,0,1,(-25994/4056813),(-25994/4056813),(-601102862/5613276921)],
    #v[0,0,0,0,1,(-789468527135/1579610196811),(-395070834838/1579610196811)],
    #v[0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,1]]
def b2Gram : GramCertificate 7 7 :=
  ⟨fun i => b2Weights.get i,fun i j => (b2Factors.get i).get j⟩

def h3Weights : Vector ℚ 4 :=
  #v[(1403/250),(12528519/5612000),(7609707/4983500),(56953417/37578800)]
def h3Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(4355/5612),(3401/5612),(3401/5612)],
    #v[0,1,(3401/9967),(3401/9967)],
    #v[0,0,1,(146161/1691046)],
    #v[0,0,0,1]]
def h3Gram : GramCertificate 4 4 :=
  ⟨fun i => h3Weights.get i,fun i j => (h3Factors.get i).get j⟩

def b3Weights : Vector ℚ 11 :=
  #v[(3347/1000),(6960519/669400),(34741632404/4350324375),(12836910431307/4342704050500),(289077055665024467/51347641725228000),(196264490416405697442/36134631958128058375),(7965240530158143092315701/1570115923331245579536000),(975538843234823735429947328/199131013253953577307892525),(224092538071231206897393/1404037101854408352256000),(27357461634274443255475333/179274030456984965517914400),(26709323/140944000)]
def b3Factors : Vector (Vector ℚ 11) 11 :=
  #v[#v[1,(-455/3347),(651/3347),(-1061/3347),(-343/3347),(-146/3347),(-343/3347),(-146/3347),(-260/3347),(1/3347),(71/6694)],
    #v[0,1,(16535849/34802595),(1696142/34802595),(583622/34802595),(90403/2320173),(583622/34802595),(90403/2320173),(883223/11600865),(63114/1288985),(-11467987/69605190)],
    #v[0,0,1,(-2129106763/34741632404),(7114776203/138966529616),(990068595/138966529616),(7114776203/138966529616),(990068595/138966529616),(1595956233/69483264808),(5088995451/69483264808),(-7925594347/69483264808)],
    #v[0,0,0,1,(-4137249393811/51347641725228),(-7044573844211/51347641725228),(-4137249393811/51347641725228),(-7044573844211/51347641725228),(-157438848318/4278970143769),(-359939765483/4278970143769),(55019/2185301)],
    #v[0,0,0,0,1,(54256743485683891/289077055665024467),(-18084537135289429/289077055665024467),(-90903039671535665/289077055665024467),(13038458978429613/289077055665024467),(-36016038436146579/289077055665024467),(39178281434816265/289077055665024467)],
    #v[0,0,0,0,0,1,(-492656996833663132247/1570115923331245579536),(-5759209822902422201/1570115923331245579536),(-9022513253529806033/65421496805468565814),(4644186258608516155/65421496805468565814),(6669543895/58447684794)],
    #v[0,0,0,0,0,0,1,(1475362274029113248684491/7965240530158143092315701),(54597053550417167614056/7965240530158143092315701),(-980245433508696588461304/7965240530158143092315701),(-1010829901680837491573944/7965240530158143092315701)],
    #v[0,0,0,0,0,0,0,1,(-180772970712381338055/1404037101854408352256),(43107538145256451641/1404037101854408352256),(-37628220054251/351427158189568)],
    #v[0,0,0,0,0,0,0,0,1,(-46945198746585244405583/224092538071231206897393),(-88573669662322981245905/224092538071231206897393)],
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

private theorem equations_checked : FiniteK3EnvelopeEquations 4 10 coeff := by
  exact finiteK3EnvelopeEquations_of_integer 4 10 denominator (numerators.get 0) numerators.get
    (by decide) (by decide +kernel) integer_equations_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h0_checked : h0Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 0) := by
  change h0Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 0) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b0_checked : b0Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 10 (by decide) 0) := by
  change b0Gram.StrictValid (Matrix.of (fun i j : Fin 7 => (finiteK3EnvelopeTableB0 coeff 4 10 (by decide) 0) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h1_checked : h1Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 1) := by
  change h1Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 1) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b1_checked : b1Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 10 (by decide) 1) := by
  change b1Gram.StrictValid (Matrix.of (fun i j : Fin 11 => (finiteK3EnvelopeTableB0 coeff 4 10 (by decide) 1) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h2_checked : h2Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 2) := by
  change h2Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 2) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b2_checked : b2Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 10 (by decide) 2) := by
  change b2Gram.StrictValid (Matrix.of (fun i j : Fin 7 => (finiteK3EnvelopeTableB0 coeff 4 10 (by decide) 2) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h3_checked : h3Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 3) := by
  change h3Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 3) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b3_checked : b3Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 10 (by decide) 3) := by
  change b3Gram.StrictValid (Matrix.of (fun i j : Fin 11 => (finiteK3EnvelopeTableB0 coeff 4 10 (by decide) 3) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem kernels_checked : ∀ s : Fin 4,∀ i,
    (∑ j,finiteK3EnvelopeFlatTableB coeff 4 10 (by decide) s i j*
      finiteK3EnvelopeKernel 4 10 s j)=0 := by
  decide +kernel

theorem valid : FiniteK3EnvelopeValid 4 10 (by decide) coeff := by
  refine ⟨equations_checked,?_⟩
  intro s
  have hk := kernels_checked s
  rw [← finiteK3EnvelopeFlatB_eq_table coeff 4 10 (by decide) (by decide) s] at hk
  fin_cases s
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h0Gram.strictValid_posDef _ h0_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 10 (by decide) (by decide)]
      exact b0Gram.strictValid_posDef _ b0_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h1Gram.strictValid_posDef _ h1_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 10 (by decide) (by decide)]
      exact b1Gram.strictValid_posDef _ b1_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h2Gram.strictValid_posDef _ h2_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 10 (by decide) (by decide)]
      exact b2Gram.strictValid_posDef _ b2_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h3Gram.strictValid_posDef _ h3_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 10 (by decide) (by decide)]
      exact b3Gram.strictValid_posDef _ b3_checked

end DittertRybin.Certificates.FiniteK3Cases.C4N10
