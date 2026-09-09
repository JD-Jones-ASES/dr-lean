import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (2,6). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block20PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-137600860387526067622378699237248000000000000000 : ℚ) / 7, (821023278258926713752748128080012880000000000000 : ℚ) / 7, (-8566572722711356786290897564283508298800000000000 : ℚ) / 21, (6606034038266898062453636403496060367028125000000 : ℚ) / 7, (-30658368345718108814813226230388714885449843750000 : ℚ) / 21, (31933152085868183964181430760120196703453593750000 : ℚ) / 21, (-7090142240810667557870627312414520165381328125000 : ℚ) / 7, (12581121048028658510227096154592655742156523437500 : ℚ) / 21, (-4966837719326615427823064762102343046728298828125 : ℚ) / 7, (19814585454754740294771980559029021022146169921875 : ℚ) / 21, (-9418580992406613877774040121641752742947347265625 : ℚ) / 21, (-6598635895328868417748002833040293837932805078125 : ℚ) / 21, (11456740645776057895471394767854888357531851359375 : ℚ) / 21, (-932408493408147621681913741858326113265325281250 : ℚ) / 7, (-2285685069143881179702364780783901673884687696875 : ℚ) / 21, (1358869450631582626048339445866220955567057081250 : ℚ) / 21, (-137841697626241137749985305396081372377741075000 : ℚ) / 21, (-142020087104394181955294208574003267569669678125 : ℚ) / 21, (107168624723431760683183412348140085575685348750 : ℚ) / 21, (-64477436836730108029010743880214321150019375 : ℚ) / 21, (-7547429098919246362504098940691007032180158000 : ℚ) / 21, (1198983599306273467978711279062798554563121500 : ℚ) / 7, (30190482945633586016222491044970212391666490 : ℚ) / 3, (-290782790854629136828408366021724619502175060 : ℚ) / 21, (6242367879859996287314959198596603709070892 : ℚ) / 7, (2362383233312534700981245212781232695347256 : ℚ) / 7, (-633032320816147167873955322873587782695060 : ℚ) / 7, (8356433174060185960097883647975600236010 : ℚ) / 21, (17253776868402529697359178279197968610215 : ℚ) / 7, (-5487312923423091153651492008501447169509 : ℚ) / 21, (-670585144389236065803057916671360997567 : ℚ) / 21, (5745568913901111841630460254675054485 : ℚ) / 1, (466409688998627950200144193414454360 : ℚ) / 21, (-1724718763436755563918145469781785275 : ℚ) / 21, (-9522949130899743952556132709420912 : ℚ) / 7, (4563079791889460643933146923264187 : ℚ) / 21]

def block20Margin0 : ℚ := (75659165793300329225584510508087092876555582040792831356684985653598880677035720989102760927 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block20_coefficient_bound_0 : ∀ i : Fin 37, block20Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block20PowerCoefficients) i := by
  decide +kernel

theorem block20_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block20PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block20Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block20PowerCoefficients
      block20Margin0 (by norm_num) block20_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block20Margin1 : ℚ := (716582138297965419161642450864434395664896673399363543536525680942557909597267587 : ℚ) / 1000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block20_coefficient_bound_1 : ∀ i : Fin 37, block20Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block20PowerCoefficients) i := by
  decide +kernel

theorem block20_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block20PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block20Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block20PowerCoefficients
      block20Margin1 (by norm_num) block20_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block20Margin2 : ℚ := (36587102111303644523308970422517168050616544061195542739158414284074420542601085960526469647 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block20_coefficient_bound_2 : ∀ i : Fin 37, block20Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block20PowerCoefficients) i := by
  decide +kernel

theorem block20_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block20PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block20Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block20PowerCoefficients
      block20Margin2 (by norm_num) block20_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block20Margin3 : ℚ := (6711239144805642985575709703209798751103392288286685568104764786676542 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block20_coefficient_bound_3 : ∀ i : Fin 37, block20Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block20PowerCoefficients) i := by
  decide +kernel

theorem block20_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block20PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block20Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block20PowerCoefficients
      block20Margin3 (by norm_num) block20_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block20Margin4 : ℚ := (28356770975770989495754067761844695247728002584663507183541533747309018859713 : ℚ) / 62774143431601029120000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block20_coefficient_bound_4 : ∀ i : Fin 37, block20Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block20PowerCoefficients) i := by
  decide +kernel

theorem block20_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block20PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block20Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block20PowerCoefficients
      block20Margin4 (by norm_num) block20_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block20Margin5 : ℚ := (15067284791780244870090782524123910078341157038366727683747862124441 : ℚ) / 33056565380087516495872

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block20_coefficient_bound_5 : ∀ i : Fin 37, block20Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block20PowerCoefficients) i := by
  decide +kernel

theorem block20_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block20PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block20Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block20PowerCoefficients
      block20Margin5 (by norm_num) block20_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block20Margin6 : ℚ := (3460704874432469553778183040884488925475248023144347051594689440740274528150892869 : ℚ) / 7000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block20_coefficient_bound_6 : ∀ i : Fin 37, block20Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block20PowerCoefficients) i := by
  decide +kernel

theorem block20_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block20PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block20Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block20PowerCoefficients
      block20Margin6 (by norm_num) block20_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block20Margin7 : ℚ := (39284740556943378336418976136161428158829979612352544624916539179748646954893679464793618687 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block20_coefficient_bound_7 : ∀ i : Fin 37, block20Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block20PowerCoefficients) i := by
  decide +kernel

theorem block20_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block20PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block20Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block20PowerCoefficients
      block20Margin7 (by norm_num) block20_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block20Margin8 : ℚ := (10115426051259875332570067698842106552912724420016639841320562239332352 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block20_coefficient_bound_8 : ∀ i : Fin 37, block20Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block20PowerCoefficients) i := by
  decide +kernel

theorem block20_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block20PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block20Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block20PowerCoefficients
      block20Margin8 (by norm_num) block20_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block20_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block20PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block20_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block20_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block20_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block20_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block20_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block20_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block20_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block20_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block20_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
