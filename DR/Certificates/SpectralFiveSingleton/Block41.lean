import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (5,6). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block41PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-157084887599645204808750153603456000000000000000 : ℚ) / 7, (920829532346062717278528089178827400000000000000 : ℚ) / 7, (-1333044160083169577025882425545164134000000000000 : ℚ) / 3, (6815166975193516062940012673188760476375000000000 : ℚ) / 7, (-29028906453900831506715760782313418580162500000000 : ℚ) / 21, (8494874379693846533769400809703007369650000000000 : ℚ) / 7, (-3994850382169978801084418812645429571918750000000 : ℚ) / 7, (8767026336820473412874531301095830880176562500000 : ℚ) / 21, (-25310797779924660866074022714302442085351406250000 : ℚ) / 21, (40450966555295268400251419399872172109058281250000 : ℚ) / 21, (-25889547323730628497066126616963924736587906250000 : ℚ) / 21, (-5327585149732559421294801714747481138245718750000 : ℚ) / 21, (18837128733595651111799967853724548264924673750000 : ℚ) / 21, (-2822807624245720389902862285977620797864204375000 : ℚ) / 7, (-816766691642245991781745434460043991206721750000 : ℚ) / 7, (2459905203061845239394222749972545119857578625000 : ℚ) / 21, (-744953064918999467537826777211664425274354500000 : ℚ) / 21, (-151092144373144968700158256392398872525799750000 : ℚ) / 21, (215981665737870223644064532409477667710261612500 : ℚ) / 21, (-30679710397293095392163904597814180100863037500 : ℚ) / 21, (-13152194516966618648965613932157807285597405000 : ℚ) / 21, (7552942310522243802686312173298245468013540000 : ℚ) / 21, (-252776561096913933219387619394596581301500700 : ℚ) / 21, (-62524368428826982847703952499199398373936050 : ℚ) / 3, (90217679064965006428641750923722108277601260 : ℚ) / 21, (1231145039627075166763970403481663323775060 : ℚ) / 7, (-4576756076066638326894594283588163394154300 : ℚ) / 21, (24501099604838332684885538786919482886850 : ℚ) / 1, (26575349920799878346888865597000739614900 : ℚ) / 7, (-21793299250341118820437438384557215424340 : ℚ) / 21, (65186769988368257501492703384136762940 : ℚ) / 3, (142504187584006841552173029757441357700 : ℚ) / 7, (-26434868418461609760148600522760713900 : ℚ) / 21, (-2836820645100873267366233568220159750 : ℚ) / 21, (202362669031619558991817820075194380 : ℚ) / 7, (45630797918894606439331469232641870 : ℚ) / 21]

def block41Margin0 : ℚ := (47772379854005134698150638204874608069235006129290418008521937024744816692381620695325373489 : ℚ) / 48103633715200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block41_coefficient_bound_0 : ∀ i : Fin 37, block41Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block41PowerCoefficients) i := by
  decide +kernel

theorem block41_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block41PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block41Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block41PowerCoefficients
      block41Margin0 (by norm_num) block41_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block41Margin1 : ℚ := (383531195787359198280371396791495899003585401243476206755198079537683812373586609 : ℚ) / 700000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block41_coefficient_bound_1 : ∀ i : Fin 37, block41Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block41PowerCoefficients) i := by
  decide +kernel

theorem block41_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block41PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block41Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block41PowerCoefficients
      block41Margin1 (by norm_num) block41_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block41Margin2 : ℚ := (2274707415425245893051546880144221563680271590200985620398630478175243430275535278058056647 : ℚ) / 6871947673600000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block41_coefficient_bound_2 : ∀ i : Fin 37, block41Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block41PowerCoefficients) i := by
  decide +kernel

theorem block41_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block41PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block41Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block41PowerCoefficients
      block41Margin2 (by norm_num) block41_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block41Margin3 : ℚ := (4920103375213038867786938565995249672829756483024469694813586325842588 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block41_coefficient_bound_3 : ∀ i : Fin 37, block41Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block41PowerCoefficients) i := by
  decide +kernel

theorem block41_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block41PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block41Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block41PowerCoefficients
      block41Margin3 (by norm_num) block41_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block41Margin4 : ℚ := (46963554572329694095833053491608922883240020119872928455149441945785631 : ℚ) / 211284394934250776821760000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block41_coefficient_bound_4 : ∀ i : Fin 37, block41Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block41PowerCoefficients) i := by
  decide +kernel

theorem block41_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block41PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block41Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block41PowerCoefficients
      block41Margin4 (by norm_num) block41_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block41Margin5 : ℚ := (3680284618446699460924828549080484004408285564736903737872826717205 : ℚ) / 16528282690043758247936

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block41_coefficient_bound_5 : ∀ i : Fin 37, block41Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block41PowerCoefficients) i := by
  decide +kernel

theorem block41_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block41PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block41Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block41PowerCoefficients
      block41Margin5 (by norm_num) block41_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block41Margin6 : ℚ := (171892473752040984766456121936897696733227110830159054375446846428882921675557369 : ℚ) / 700000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block41_coefficient_bound_6 : ∀ i : Fin 37, block41Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block41PowerCoefficients) i := by
  decide +kernel

theorem block41_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block41PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block41Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block41PowerCoefficients
      block41Margin6 (by norm_num) block41_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block41Margin7 : ℚ := (2052613662359408310507631833867502789158464623850874473634018356130516374375743711199441687 : ℚ) / 6871947673600000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block41_coefficient_bound_7 : ∀ i : Fin 37, block41Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block41PowerCoefficients) i := by
  decide +kernel

theorem block41_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block41PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block41Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block41PowerCoefficients
      block41Margin7 (by norm_num) block41_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block41Margin8 : ℚ := (7789028901132260068469168779607758086103138920606203615432748449660928 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block41_coefficient_bound_8 : ∀ i : Fin 37, block41Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block41PowerCoefficients) i := by
  decide +kernel

theorem block41_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block41PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block41Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block41PowerCoefficients
      block41Margin8 (by norm_num) block41_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block41_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block41PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block41_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block41_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block41_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block41_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block41_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block41_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block41_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block41_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block41_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
