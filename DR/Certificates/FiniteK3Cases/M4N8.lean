import DR.Certificates.FiniteK3EnvelopeSparseEquations

/-! Exact mathematical rational data and kernel checks for K3 on 4x8.
Reproduce with scripts/generate_finite_k3_envelope.py --case 4 8 --check. -/
namespace DittertRybin.Certificates.FiniteK3Cases.C4N8
open scoped BigOperators

def numerators : Vector ℤ 93 :=
  #v[25125,-1347,-3356,-268,96699,-10368,143,35987,-7863,104943,3854,-12668,-7445,101711,414,-2354,-6416,103194,-21324,-2329,3663,41547,-11307,139552,-13750,10638,48416,-18348,208224,-20418,-7554,81308,-37316,-28292,109696,12894,18204,-1636,107212,-704,-29568,8064,3829,-9773,140288,-2944,33024,-16320,-256,55264,-14592,119520,2848,-13750,-18540,136608,-7008,74590,-11556,101036,3072,-6144,34720,-26336,-256,-9216,-5600,-3705,295296,21376,138144,15936,-2592,12928,-59648,160128,-9152,109056,-27072,7296,-23424,80960,-24864,162368,41472,27776,-8960,-57920,-33728,137152,18592,63968,-13750]
def denominator : Nat := 32000
def coeff (i : Fin 93) : ℚ := (numerators.get i:ℚ)/denominator

def h0Weights : Vector ℚ 4 :=
  #v[(107067/32000),(8922743399/3426144000),(144585081699691/57105557753600),(115649572519029/47582893139200)]
def h0Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(43850/107067),(43850/107067),(43850/107067)],
    #v[0,1,(-1487916346/8922743399),(-1487916346/8922743399)],
    #v[0,0,1,(-1487916346/7434827053)],
    #v[0,0,0,1]]
def h0Gram : GramCertificate 4 4 :=
  ⟨fun i => h0Weights.get i,fun i j => (h0Factors.get i).get j⟩

def b0Weights : Vector ℚ 7 :=
  #v[(201/256),(2625430139/804000000),(270021201715733/84013764448000),(231262939353537/73468284896000),(353577967107/2330474272000),(2020651961/4939662000),(2020651961/6586216000)]
def b0Factors : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(-3356/25125),(-3356/25125),(-3356/25125),(-449/8375),(-4/375),(-4/375)],
    #v[0,1,(-329546236/2625430139),(-329546236/2625430139),(-927657/2625430139),(95932342/2625430139),(-187955033/2625430139)],
    #v[0,0,1,(-329546236/2295883903),(-927657/2295883903),(-18382036465599/270021201715733),(7559155754398/270021201715733)],
    #v[0,0,0,1,(-103073/218481963),(-6127345488533/77087646451179),(-6127345488533/77087646451179)],
    #v[0,0,0,0,1,(-1/3),(-1/3)],
    #v[0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,1]]
def b0Gram : GramCertificate 7 7 :=
  ⟨fun i => b0Weights.get i,fun i j => (b0Factors.get i).get j⟩

def h1Weights : Vector ℚ 4 :=
  #v[(76651/16000),(2595627127/1226416000),(86260822940163/41530034032000),(72639318406239/35866353968000)]
def h1Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(33382/76651),(33382/76651),(33382/76651)],
    #v[0,1,(-353980004/2595627127),(-353980004/2595627127)],
    #v[0,0,1,(-353980004/2241647123)],
    #v[0,0,0,1]]
def h1Gram : GramCertificate 4 4 :=
  ⟨fun i => h1Weights.get i,fun i j => (h1Factors.get i).get j⟩

def b1Weights : Vector ℚ 11 :=
  #v[(51597/16000),(56634937/18345600),(10759399101981/1812317984000),(69525726558103/11954887891090),(27107058801807763092713/5339575799662310400000),(1100759932496368723462326333/216856470414462104741704000),(14156276221724764644871/2968358945425990304000),(2156764427264444388899431/453000839095192468635872),(5424798347/23391424000),(307419031/690307200),(307419031/920409600)]
def b1Factors : Vector (Vector ℚ 11) 11 :=
  #v[#v[1,(-3554/17199),(407/11466),(13849/34398),(407/11466),(13849/34398),(407/11466),(13849/34398),(-2329/103194),(-3769/34398),(-3769/34398)],
    #v[0,1,(48505677/113269874),(14043865/113269874),(48505677/113269874),(14043865/113269874),(48505677/113269874),(14043865/113269874),(-2329/81870),(-3769/27290),(-3769/27290)],
    #v[0,0,1,(-512316840223/3586466367327),(3571519437689/10759399101981),(-2493967686095/10759399101981),(3571519437689/10759399101981),(-2493967686095/10759399101981),(675321401465/10759399101981),(-24732159467/3586466367327),(-1248691801907/10759399101981)],
    #v[0,0,0,1,(-62812656384416957/333723487478894400),(101804939758013507/333723487478894400),(-62812656384416957/333723487478894400),(101804939758013507/333723487478894400),(32540905/444391104),(-1191739/148130368),(-60169219/444391104)],
    #v[0,0,0,0,1,(-306185867117696351063/27107058801807763092713),(5929633733372082257513/27107058801807763092713),(-3125815612826875136663/27107058801807763092713),(1757204124830726884125/27107058801807763092713),(-3653440038324524605125/27107058801807763092713),(211249789644954055425/27107058801807763092713)],
    #v[0,0,0,0,0,1,(-62812656384416957/556567302267373182),(121038875030465275/556567302267373182),(32540905/496313802),(-1621658162065/11896145520138),(93767775581/11896145520138)],
    #v[0,0,0,0,0,0,1,(579709681049035288629/14156276221724764644871),(2623989741709106161985/42468828665174293934613),(-5455592237149091220745/42468828665174293934613),(-5455592237149091220745/42468828665174293934613)],
    #v[0,0,0,0,0,0,0,1,(6508181/109647300),(-324331632413/2628136133700),(-324331632413/2628136133700)],
    #v[0,0,0,0,0,0,0,0,1,(-1/3),(-1/3)],
    #v[0,0,0,0,0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,0,0,0,0,1]]
def b1Gram : GramCertificate 11 11 :=
  ⟨fun i => b1Weights.get i,fun i j => (b1Factors.get i).get j⟩

def h2Weights : Vector ℚ 4 :=
  #v[(1119/250),(1471401/373000),(148117/51000),(18817166473/7583590400)]
def h2Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(257/746),(2183/4476),(2183/4476)],
    #v[0,1,(37/102),(37/102)],
    #v[0,0,1,(904387/2369872)],
    #v[0,0,0,1]]
def h2Gram : GramCertificate 4 4 :=
  ⟨fun i => h2Weights.get i,fun i j => (h2Factors.get i).get j⟩

def b2Weights : Vector ℚ 7 :=
  #v[(26803/8000),(2709221/875200),(660763457/177472000),(3880898990269/1057221531200),(93801834569057/177817509261875),(120100089503880651/328306420991699500),(310703029/2132320000)]
def b2Factors : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(-1056/3829),(1/28),(1/28),(-176/26803),(288/3829),(-9773/107212)],
    #v[0,1,(547/11092),(547/11092),(7533408/94822735),(207856/13546105),(-9773/77644)],
    #v[0,0,1,(-78351963/660763457),(-3432736/660763457),(-3432736/660763457),(21140839/660763457)],
    #v[0,0,0,1,(-1716368/291205747),(-1716368/291205747),(-5657484602393/38808989902690)],
    #v[0,0,0,0,1,(-103867199894119/187603669138114),(-83736469243995/375207338276228)],
    #v[0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,1]]
def b2Gram : GramCertificate 7 7 :=
  ⟨fun i => b2Weights.get i,fun i j => (b2Factors.get i).get j⟩

def h3Weights : Vector ℚ 4 :=
  #v[(529/100),(617974/330625),(6744011/4772000),(120850804107/86323340800)]
def h3Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(2127/2645),(3307/5290),(3307/5290)],
    #v[0,1,(3307/9544),(3307/9544)],
    #v[0,0,1,(2613791/26976044)],
    #v[0,0,0,1]]
def h3Gram : GramCertificate 4 4 :=
  ⟨fun i => h3Weights.get i,fun i j => (h3Factors.get i).get j⟩

def b3Weights : Vector ℚ 11 :=
  #v[(25259/8000),(58254081/6314750),(533274214447/77672108000),(552616424408399/196901248411200),(529903393009103581/106272389309307500),(835333544674850130708933/179107346837077010378000),(299785274039606419594584317/69611128722904177559077750),(29895374658711586538636997372/7494631850990160489864607925),(47164547674304202624854863/188633393015771854184883000),(715411624545048320069000132/3537341075572815196864114725),(23694791/135360000)]
def b3Factors : Vector (Vector ℚ 11) 11 :=
  #v[#v[1,(768/25259),(8680/25259),(-6584/25259),(-2304/25259),(-1400/25259),(-2304/25259),(-1400/25259),(-1536/25259),(-64/25259),(-285/7772)],
    #v[0,1,(36069941/77672108),(28038079/233016324),(-608265/77672108),(2584759/58254081),(-608265/77672108),(2584759/58254081),(4255117/58254081),(2097521/38836054),(-11748464/58254081)],
    #v[0,0,1,(-816543621/41021093419),(41672420917/533274214447),(-16384654512/533274214447),(41672420917/533274214447),(-16384654512/533274214447),(19500138572/533274214447),(34126893750/533274214447),(-74583072843/533274214447)],
    #v[0,0,0,1,(-227123160604152/2763082122041995),(-381069511981688/2763082122041995),(-227123160604152/2763082122041995),(-381069511981688/2763082122041995),(-132051709211216/2763082122041995),(-241490856946464/2763082122041995),(20260063/967179148)],
    #v[0,0,0,0,1,(3503341016520076729/13777488218236693106),(-39078979352928774/529903393009103581),(-5078792054542359741/13777488218236693106),(255750293808270909/6888744109118346553),(-1082195740858456944/6888744109118346553),(5099204113158709465/27554976436473386212)],
    #v[0,0,0,0,0,1,(-104155959281376937914070/278444514891616710236311),(5950237758062491769561/278444514891616710236311),(-49576751674057478715810/278444514891616710236311),(22943862885892410573348/278444514891616710236311),(446226683809/3024459092742)],
    #v[0,0,0,0,0,0,1,(81419773934352868959576913/299785274039606419594584317),(-7785987202138640670400167/299785274039606419594584317),(-48542572584830478450906963/299785274039606419594584317),(-46905177544413333433581968/299785274039606419594584317)],
    #v[0,0,0,0,0,0,0,1,(-10513430283925292194590/62877797671923951394961),(1222326180608530904499/62877797671923951394961),(-42456929817208/345053506139505)],
    #v[0,0,0,0,0,0,0,0,1,(-20619269194379201328388383/47164547674304202624854863),(-13272639239962500648233240/47164547674304202624854863)],
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

private theorem equations_checked : FiniteK3EnvelopeEquations 4 8 coeff := by
  exact finiteK3EnvelopeEquations_of_integer 4 8 denominator (numerators.get 0) numerators.get
    (by decide) (by decide +kernel) integer_equations_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h0_checked : h0Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 0) := by
  change h0Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 0) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b0_checked : b0Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 8 (by decide) 0) := by
  change b0Gram.StrictValid (Matrix.of (fun i j : Fin 7 => (finiteK3EnvelopeTableB0 coeff 4 8 (by decide) 0) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h1_checked : h1Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 1) := by
  change h1Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 1) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b1_checked : b1Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 8 (by decide) 1) := by
  change b1Gram.StrictValid (Matrix.of (fun i j : Fin 11 => (finiteK3EnvelopeTableB0 coeff 4 8 (by decide) 1) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h2_checked : h2Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 2) := by
  change h2Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 2) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b2_checked : b2Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 8 (by decide) 2) := by
  change b2Gram.StrictValid (Matrix.of (fun i j : Fin 7 => (finiteK3EnvelopeTableB0 coeff 4 8 (by decide) 2) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h3_checked : h3Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 3) := by
  change h3Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 3) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b3_checked : b3Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 8 (by decide) 3) := by
  change b3Gram.StrictValid (Matrix.of (fun i j : Fin 11 => (finiteK3EnvelopeTableB0 coeff 4 8 (by decide) 3) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem kernels_checked : ∀ s : Fin 4,∀ i,
    (∑ j,finiteK3EnvelopeFlatTableB coeff 4 8 (by decide) s i j*
      finiteK3EnvelopeKernel 4 8 s j)=0 := by
  decide +kernel

theorem valid : FiniteK3EnvelopeValid 4 8 (by decide) coeff := by
  refine ⟨equations_checked,?_⟩
  intro s
  have hk := kernels_checked s
  rw [← finiteK3EnvelopeFlatB_eq_table coeff 4 8 (by decide) (by decide) s] at hk
  fin_cases s
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h0Gram.strictValid_posDef _ h0_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 8 (by decide) (by decide)]
      exact b0Gram.strictValid_posDef _ b0_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h1Gram.strictValid_posDef _ h1_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 8 (by decide) (by decide)]
      exact b1Gram.strictValid_posDef _ b1_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h2Gram.strictValid_posDef _ h2_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 8 (by decide) (by decide)]
      exact b2Gram.strictValid_posDef _ b2_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h3Gram.strictValid_posDef _ h3_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 8 (by decide) (by decide)]
      exact b3Gram.strictValid_posDef _ b3_checked

end DittertRybin.Certificates.FiniteK3Cases.C4N8
