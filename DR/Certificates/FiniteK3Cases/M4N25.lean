import DR.Certificates.FiniteK3EnvelopeSparseEquations

/-! Exact mathematical rational data and kernel checks for K3 on 4x25.
Reproduce with scripts/generate_finite_k3_envelope.py --case 4 25 --check. -/
namespace DittertRybin.Certificates.FiniteK3Cases.C4N25
open scoped BigOperators

def numerators : Vector ℤ 93 :=
  #v[18540,-2404,-1636,612,78606,-1372,223,21258,-1581,86462,1351,7603,-2871,79206,1326,-5413,-1739,78968,-22986,-2473,-32067,22545,427,115116,-2920,10138,52678,-4012,247738,35962,-5940,109834,30480,-14160,95164,340,13284,-590,77432,-628,-30842,400,4041,-1025,186722,-5714,-53704,1628,-386,16768,-1556,71110,-306,-2920,-2100,106074,-1924,40244,-2590,72936,-25924,-5756,-14380,-23586,1166,-25076,1808,3110,287424,17620,128982,10374,13416,-3138,-22620,116300,-1828,91984,-4550,5852,-7220,66298,-5028,160424,11632,8666,-3740,-24502,-12986,93518,3182,37014,-2920]
def denominator : Nat := 20000
def coeff (i : Fin 93) : ℚ := (numerators.get i:ℚ)/denominator

def h0Weights : Vector ℚ 4 :=
  #v[(39989/10000),(5707066719/1599560000),(99732542082701/28535333595000),(166213108730141/48916076260000)]
def h0Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(22839/79978),(22839/79978),(22839/79978)],
    #v[0,1,(-815459093/5707066719),(-815459093/5707066719)],
    #v[0,0,1,(-815459093/4891607626)],
    #v[0,0,0,1]]
def h0Gram : GramCertificate 4 4 :=
  ⟨fun i => h0Weights.get i,fun i j => (h0Factors.get i).get j⟩

def b0Weights : Vector ℚ 7 :=
  #v[(927/1000),(200041123/46350000),(34276303056193/8001644920000),(1156328758596/271658141875),(257869309517/3128158720000),(1180432811/5677848000),(1180432811/7570464000)]
def b0Factors : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(-409/4635),(-409/4635),(-409/4635),(-601/4635),(17/515),(17/515)],
    #v[0,1,(34570781/400082246),(34570781/400082246),(50369/400082246),(6512193/400082246),(-13056777/400082246)],
    #v[0,0,1,(34570781/434653027),(50369/434653027),(-1175602214825/34276303056193),(659502865169/34276303056193)],
    #v[0,0,0,1,(50369/469223808),(-1175602214825/37002520275072),(-1175602214825/37002520275072)],
    #v[0,0,0,0,1,(-1/3),(-1/3)],
    #v[0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,1]]
def b0Gram : GramCertificate 7 7 :=
  ⟨fun i => b0Weights.get i,fun i j => (b0Factors.get i).get j⟩

def h1Weights : Vector ℚ 4 :=
  #v[(29509/5000),(1994722391/590180000),(161969944038/49868059775),(1953582658187/640276492800)]
def h1Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(28345/59018),(28345/59018),(28345/59018)],
    #v[0,1,(-394031159/1994722391),(-394031159/1994722391)],
    #v[0,0,1,(-394031159/1600691232)],
    #v[0,0,0,1]]
def h1Gram : GramCertificate 4 4 :=
  ⟨fun i => h1Weights.get i,fun i j => (h1Factors.get i).get j⟩

def b1Weights : Vector ℚ 11 :=
  #v[(9871/2500),(1426897207/394840000),(14411764138751/1240780180000),(39926858014457481/3602941034687750),(152783014532370466786249/15970743205782992400000),(1441270920992895182788859487/152783014532370466786249000),(266879937555610704085273/30362583584836176900000),(5822663596698700846728442543/667199843889026760213182500),(41738891097/851092517500),(289149421/2473408500),(289149421/3297878000)]
def b1Factors : Vector (Vector ℚ 11) 11 :=
  #v[#v[1,(-11493/39484),(-32067/78968),(22545/78968),(-32067/78968),(22545/78968),(-32067/78968),(22545/78968),(-2473/78968),(427/78968),(427/78968)],
    #v[0,1,(22679163/124078018),(-43783641/124078018),(22679163/124078018),(-43783641/124078018),(22679163/124078018),(-43783641/124078018),(-2473/55982),(427/55982),(427/55982)],
    #v[0,0,1,(3088224294791/14411764138751),(5856336641615/14411764138751),(2748126447453/14411764138751),(5856336641615/14411764138751),(2748126447453/14411764138751),(602855786195/14411764138751),(-364005907407/14411764138751),(-873966561387/14411764138751)],
    #v[0,0,0,1,(173436596070112541/1597074320578299240),(611819182475162419/1597074320578299240),(173436596070112541/1597074320578299240),(611819182475162419/1597074320578299240),(11826035/343291846),(-7140591/343291846),(-17144331/343291846)],
    #v[0,0,0,0,1,(18013377264095938334351/152783014532370466786249),(42661545979855577589769/152783014532370466786249),(13635796551390820117511/152783014532370466786249),(3944369142042529289700/152783014532370466786249),(-8945595907401844747620/152783014532370466786249),(845780799996045214380/152783014532370466786249)],
    #v[0,0,0,0,0,1,(173436596070112541/3036258358483617690),(827364855430156031/3036258358483617690),(2365207/102416586),(-640953292541/12237587166830),(60600321559/12237587166830)],
    #v[0,0,0,0,0,0,1,(22548991401564053696293/266879937555610704085273),(5027063118111689582915/266879937555610704085273),(-11401081804514788210659/266879937555610704085273),(-11401081804514788210659/266879937555610704085273)],
    #v[0,0,0,0,0,0,0,1,(11826035/680874014),(-1922859877623/48813900685702),(-1922859877623/48813900685702)],
    #v[0,0,0,0,0,0,0,0,1,(-1/3),(-1/3)],
    #v[0,0,0,0,0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,0,0,0,0,1]]
def b1Gram : GramCertificate 11 11 :=
  ⟨fun i => b1Weights.get i,fun i j => (b1Factors.get i).get j⟩

def h2Weights : Vector ℚ 4 :=
  #v[(48109/5000),(265390499/30068125),(44173187/8569000),(4922069734681/1104329675000)]
def h2Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(-13833/48109),(4581/48109),(4581/48109)],
    #v[0,1,(4581/34276),(4581/34276)],
    #v[0,0,1,(81268356/220865935)],
    #v[0,0,0,1]]
def h2Gram : GramCertificate 4 4 :=
  ⟨fun i => h2Weights.get i,fun i j => (h2Factors.get i).get j⟩

def b2Weights : Vector ℚ 7 :=
  #v[(9679/2500),(252224283/77432000),(546725923/155300000),(239953853568/68340740375),(46821353687513/408080375040000),(2108815094234315273/20133182085630590000),(741267997/8883600000)]
def b2Factors : Vector (Vector ℚ 7) 7 :=
  #v[#v[1,(-15421/38716),(4041/77432),(4041/77432),(-157/19358),(50/9679),(-1025/77432)],
    #v[0,1,(1347/15530),(1347/15530),(967002/420373805),(-3024208/420373805),(-205/9318)],
    #v[0,0,1,(-28117027/546725923),(-2843732/546725923),(-2843732/546725923),(-995415/546725923)],
    #v[0,0,0,1,(-710933/129652224),(-710933/129652224),(-43938203263/1599692357120)],
    #v[0,0,0,0,1,(-13817480060135/46821353687513),(-16501936813689/46821353687513)],
    #v[0,0,0,0,0,1,(-1/2)],
    #v[0,0,0,0,0,0,1]]
def b2Gram : GramCertificate 7 7 :=
  ⟨fun i => b2Weights.get i,fun i j => (b2Factors.get i).get j⟩

def h3Weights : Vector ℚ 4 :=
  #v[(7383/1250),(386284269/196880000),(12127513/5649000),(2524883427011/1212751300000)]
def h3Factors : Vector (Vector ℚ 4) 4 :=
  #v[#v[1,(16089/19688),(35663/59064),(35663/59064)],
    #v[0,1,(1877/5649),(1877/5649)],
    #v[0,0,1,(-21085319/121275130)],
    #v[0,0,0,1]]
def h3Gram : GramCertificate 4 4 :=
  ⟨fun i => h3Weights.get i,fun i j => (h3Factors.get i).get j⟩

def b3Weights : Vector ℚ 11 :=
  #v[(9117/2500),(1268218943/91170000),(145487704873629/12682189430000),(5977167112173584979/1939836064981720000),(112467179187772231612877/14942917780433962447500),(6739769383884865342320901257/899737433502177852903016000),(40768905936209208326513046841627/5616474486570721118600751047500),(337621234364946069373643290712933487/46593035355667666658872053533288000),(1573291780091666265848490011473/27647807039103813178422375705000),(1203976258364382051004047994596114/22616069338817702571572043914924375),(416030603/4606854000)]
def b3Factors : Vector (Vector ℚ 11) 11 :=
  #v[#v[1,(-6481/18234),(-3595/18234),(-3931/12156),(-6269/18234),(226/9117),(-6269/18234),(226/9117),(-1439/18234),(583/36468),(1555/36468)],
    #v[0,1,(564665252/1268218943),(-207532893/2536437886),(20527447/1268218943),(-11375161/1268218943),(20527447/1268218943),(-11375161/1268218943),(70994611/1268218943),(98358181/2536437886),(-196148585/2536437886)],
    #v[0,0,1,(-8640378913163/96991803249086),(-2132075118048/48495901624543),(3145925039340/48495901624543),(-2132075118048/48495901624543),(3145925039340/48495901624543),(1461552470330/145487704873629),(16545709998839/290975409747258),(-5253646490375/96991803249086)],
    #v[0,0,0,1,(-662569958331996880/5977167112173584979),(-2266662199685475146/5977167112173584979),(-662569958331996880/5977167112173584979),(-2266662199685475146/5977167112173584979),(25354942989384236/1992389037391194993),(-107790274607901089/1992389037391194993),(95836545/4731305921)],
    #v[0,0,0,0,1,(30955173821451321727243/449868716751088926451508),(-20374557075171637897385/224934358375544463225754),(-38517152197094419044175/224934358375544463225754),(2846044266865463046786/112467179187772231612877),(-20291715401277610587921/449868716751088926451508),(28915990570581578728767/449868716751088926451508)],
    #v[0,0,0,0,0,1,(-372461035195303749612255674/2246589794628288447440300419),(-177867330900426234649471606/2246589794628288447440300419),(-8134380144544615138381612/172814599586791419033869263),(4932890574986447273193011/172814599586791419033869263),(22888835936933/380602529213349)],
    #v[0,0,0,0,0,0,1,(971894580181480603259819133029/23296517677833833329436026766644),(239513558239939288846438991691/11648258838916916664718013383322),(-1074475363011571777107171071973/23296517677833833329436026766644),(-10790813506440317057341480184767/163075623744836833306052187366508)],
    #v[0,0,0,0,0,0,0,1,(-86743049715126519215064434/1843187135940254211894825047),(41518725335895206321876785/1843187135940254211894825047),(-609369650338604419/9593256076735608627)],
    #v[0,0,0,0,0,0,0,0,1,(-399510371445014957338013423065/1573291780091666265848490011473),(-586890704323325654255238294204/1573291780091666265848490011473)],
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

private theorem equations_checked : FiniteK3EnvelopeEquations 4 25 coeff := by
  exact finiteK3EnvelopeEquations_of_integer 4 25 denominator (numerators.get 0) numerators.get
    (by decide) (by decide +kernel) integer_equations_checked

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h0_checked : h0Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 0) := by
  change h0Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 0) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b0_checked : b0Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 25 (by decide) 0) := by
  change b0Gram.StrictValid (Matrix.of (fun i j : Fin 7 => (finiteK3EnvelopeTableB0 coeff 4 25 (by decide) 0) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h1_checked : h1Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 1) := by
  change h1Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 1) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b1_checked : b1Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 25 (by decide) 1) := by
  change b1Gram.StrictValid (Matrix.of (fun i j : Fin 11 => (finiteK3EnvelopeTableB0 coeff 4 25 (by decide) 1) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h2_checked : h2Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 2) := by
  change h2Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 2) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b2_checked : b2Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 25 (by decide) 2) := by
  change b2Gram.StrictValid (Matrix.of (fun i j : Fin 7 => (finiteK3EnvelopeTableB0 coeff 4 25 (by decide) 2) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem h3_checked : h3Gram.StrictValid (finiteK3EnvelopeTableH coeff 4 (by decide) 3) := by
  change h3Gram.StrictValid (Matrix.of (fun i j : Fin 4 => (finiteK3EnvelopeTableH coeff 4 (by decide) 3) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem b3_checked : b3Gram.StrictValid (finiteK3EnvelopeTableB0 coeff 4 25 (by decide) 3) := by
  change b3Gram.StrictValid (Matrix.of (fun i j : Fin 11 => (finiteK3EnvelopeTableB0 coeff 4 25 (by decide) 3) i j))
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
private theorem kernels_checked : ∀ s : Fin 4,∀ i,
    (∑ j,finiteK3EnvelopeFlatTableB coeff 4 25 (by decide) s i j*
      finiteK3EnvelopeKernel 4 25 s j)=0 := by
  decide +kernel

theorem valid : FiniteK3EnvelopeValid 4 25 (by decide) coeff := by
  refine ⟨equations_checked,?_⟩
  intro s
  have hk := kernels_checked s
  rw [← finiteK3EnvelopeFlatB_eq_table coeff 4 25 (by decide) (by decide) s] at hk
  fin_cases s
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h0Gram.strictValid_posDef _ h0_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 25 (by decide) (by decide)]
      exact b0Gram.strictValid_posDef _ b0_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h1Gram.strictValid_posDef _ h1_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 25 (by decide) (by decide)]
      exact b1Gram.strictValid_posDef _ b1_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h2Gram.strictValid_posDef _ h2_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 25 (by decide) (by decide)]
      exact b2Gram.strictValid_posDef _ b2_checked
  · refine ⟨?_,?_,hk⟩
    · rw [finiteK3EnvelopeH_eq_table coeff 4 (by decide) (by decide)]
      exact h3Gram.strictValid_posDef _ h3_checked
    · rw [finiteK3EnvelopeB0_eq_table coeff 4 25 (by decide) (by decide)]
      exact b3Gram.strictValid_posDef _ b3_checked

end DittertRybin.Certificates.FiniteK3Cases.C4N25
