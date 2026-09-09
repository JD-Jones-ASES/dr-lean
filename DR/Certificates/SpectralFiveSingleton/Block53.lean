import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (7,4). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block53PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-24958839973385448153058629485504000000000000000 : ℚ) / 1, (446398192409048074902242652767074520000000000000 : ℚ) / 3, (-1502437480934983645564924932705489516400000000000 : ℚ) / 3, (3143972257563969885430904853703247918825000000000 : ℚ) / 3, (-3792443687012645940243953128002622585205000000000 : ℚ) / 3, (1244802104660302234304508475534258793333750000000 : ℚ) / 3, (4034205274237141427128778612211880923735625000000 : ℚ) / 3, (-6983005884475302899865403245342684857025625000000 : ℚ) / 3, (3363399540088809091765885235797979490124656250000 : ℚ) / 3, (3662189198170690446775097893878568162588843750000 : ℚ) / 3, (-6171713368773231407971042636161411661927793750000 : ℚ) / 3, (2431041310723130562498728689213874304765493750000 : ℚ) / 3, (1592879642999373791266249526472614568044767750000 : ℚ) / 3, (-592607115615627926940032407135174929333613375000 : ℚ) / 1, (185710324011490867791080088506135624365038550000 : ℚ) / 3, (276534397545730192354673510295751729469628725000 : ℚ) / 3, (-54645950589989326912253102641301385740829700000 : ℚ) / 1, (4200660584482708779631950239170779485187600000 : ℚ) / 1, (28215857979233585787968677828014474258133952500 : ℚ) / 3, (-7900374427142976316268032772623834730653607500 : ℚ) / 3, (-1232713804229078734592549603127791029645049000 : ℚ) / 3, (1002359233364739316722268010039601592876150000 : ℚ) / 3, (-26918230059786484449044219016564485623956820 : ℚ) / 1, (-13130162729815098031544431240804512513777090 : ℚ) / 1, (14140378896963615836879462427525437802197228 : ℚ) / 3, (3525973153923540001644167465264317686116 : ℚ) / 3, (-497773415211205307690029534911460362288080 : ℚ) / 3, (93184033926622126222745687171879927378140 : ℚ) / 3, (9721402594995131080200172979995708005250 : ℚ) / 3, (-2388060050029628354061319835093437456882 : ℚ) / 3, (249913242260977263516850244903296171106 : ℚ) / 3, (70389167667242420466479824250240780060 : ℚ) / 3, (-779091375324916138373785464882561130 : ℚ) / 1, (120200996385648880226346610403940730 : ℚ) / 3, (150383238358791789917448929036271902 : ℚ) / 3, (9126159583778921287866293846528374 : ℚ) / 3]

def block53Margin0 : ℚ := (31053308486716755009312165170991651740263755168975523152533463444090008612367258878430323069 : ℚ) / 34359738368000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block53_coefficient_bound_0 : ∀ i : Fin 37, block53Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block53PowerCoefficients) i := by
  decide +kernel

theorem block53_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block53PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block53Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block53PowerCoefficients
      block53Margin0 (by norm_num) block53_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block53Margin1 : ℚ := (210067692548795094523677742252164049889724192976704769846437856888043381908188399 : ℚ) / 500000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block53_coefficient_bound_1 : ∀ i : Fin 37, block53Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block53PowerCoefficients) i := by
  decide +kernel

theorem block53_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block53PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block53Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block53PowerCoefficients
      block53Margin1 (by norm_num) block53_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block53Margin2 : ℚ := (6566015473648340057691864364321609498528467803017666022884540538193424773674302570801433589 : ℚ) / 34359738368000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block53_coefficient_bound_2 : ∀ i : Fin 37, block53Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block53PowerCoefficients) i := by
  decide +kernel

theorem block53_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block53PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block53Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block53PowerCoefficients
      block53Margin2 (by norm_num) block53_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block53Margin3 : ℚ := (1463760987402922433440181839068895141091851998034060462427689164919128 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block53_coefficient_bound_3 : ∀ i : Fin 37, block53Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block53PowerCoefficients) i := by
  decide +kernel

theorem block53_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block53PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block53Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block53PowerCoefficients
      block53Margin3 (by norm_num) block53_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block53Margin4 : ℚ := (21987307097381492669439312049168123099866157609797565885883608159754007 : ℚ) / 265820464405916155904000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block53_coefficient_bound_4 : ∀ i : Fin 37, block53Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block53PowerCoefficients) i := by
  decide +kernel

theorem block53_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block53PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block53Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block53PowerCoefficients
      block53Margin4 (by norm_num) block53_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block53Margin5 : ℚ := (196615868917579449504985552665859053870393648864568127144441054637 : ℚ) / 2361183241434822606848

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block53_coefficient_bound_5 : ∀ i : Fin 37, block53Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block53PowerCoefficients) i := by
  decide +kernel

theorem block53_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block53PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block53Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block53PowerCoefficients
      block53Margin5 (by norm_num) block53_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block53Margin6 : ℚ := (52668320911322543516693420609024828057063302035579243475766817345740913031708899 : ℚ) / 500000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block53_coefficient_bound_6 : ∀ i : Fin 37, block53Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block53PowerCoefficients) i := by
  decide +kernel

theorem block53_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block53PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block53Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block53PowerCoefficients
      block53Margin6 (by norm_num) block53_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block53Margin7 : ℚ := (5226719225477788112782350804728589186349028150603070434888668811340828498730039298569397749 : ℚ) / 34359738368000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block53_coefficient_bound_7 : ∀ i : Fin 37, block53Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block53PowerCoefficients) i := by
  decide +kernel

theorem block53_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block53PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block53Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block53PowerCoefficients
      block53Margin7 (by norm_num) block53_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block53Margin8 : ℚ := (3213236978023287147747797589958062234577581350250365916491923219611648 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block53_coefficient_bound_8 : ∀ i : Fin 37, block53Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block53PowerCoefficients) i := by
  decide +kernel

theorem block53_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block53PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block53Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block53PowerCoefficients
      block53Margin8 (by norm_num) block53_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block53_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block53PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block53_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block53_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block53_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block53_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block53_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block53_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block53_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block53_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block53_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
