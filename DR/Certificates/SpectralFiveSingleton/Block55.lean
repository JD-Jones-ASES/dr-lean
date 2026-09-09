import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (7,6). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block55PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-24296319867770185180904446168704000000000000000 : ℚ) / 1, (140598755218450577651750132835215840000000000000 : ℚ) / 1, (-465209080317218950692556596194778948800000000000 : ℚ) / 1, (979475265297409492848908779527754770850000000000 : ℚ) / 1, (-1294377153938235425984957221948749101485000000000 : ℚ) / 1, (945370011951378726383584376395069845270000000000 : ℚ) / 1, (-205615228401963980655577351032766457247500000000 : ℚ) / 1, (262154317616344715823873591434066093548125000000 : ℚ) / 1, (-1572265452993022141113371357587214598855062500000 : ℚ) / 1, (2670196957433287212951347914236852257054812500000 : ℚ) / 1, (-1839314481721337051164131323965746223521712500000 : ℚ) / 1, (-184635923122909168661840456949890720115537500000 : ℚ) / 1, (1150697594529530898168798188843342464164220500000 : ℚ) / 1, (-613638225839237252740389853947771845331204750000 : ℚ) / 1, (-109158517253340044755517879904308964086295900000 : ℚ) / 1, (155980279661001405994207555194196404537137550000 : ℚ) / 1, (-60443861727474654763355276462096243303669200000 : ℚ) / 1, (-5372298528863859537391801671551526983295850000 : ℚ) / 1, (15318967197522285070417967368936036217663630000 : ℚ) / 1, (-2786811551499170786549770879261265624633160000 : ℚ) / 1, (-923880276003900496050504668990726756541908000 : ℚ) / 1, (526245764385345955530130952087869618459032000 : ℚ) / 1, (-20254459050221846808260753480140600251838320 : ℚ) / 1, (-25040710481204463911532461251062243432713560 : ℚ) / 1, (7336591522784398604687435216055358315148176 : ℚ) / 1, (132468159053263139999888443308893830226768 : ℚ) / 1, (-304654017097546303930750723449091938667680 : ℚ) / 1, (48007817042498315297811421725977831417260 : ℚ) / 1, (5701904352332923471879133755185861790270 : ℚ) / 1, (-1513496695382908128275139991031019142134 : ℚ) / 1, (102176571995097016650212774168195098058 : ℚ) / 1, (37290581968980658677899050559018929810 : ℚ) / 1, (-1783259205975955992598381551331255640 : ℚ) / 1, (-58345473023833114227393319086275525 : ℚ) / 1, (70628539387506434314791317594871764 : ℚ) / 1, (4563079791889460643933146923264187 : ℚ) / 1]

def block55Margin0 : ℚ := (63250406675121589449795893116038927340033070993133391185534977434544233424914373821844569467 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block55_coefficient_bound_0 : ∀ i : Fin 37, block55Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block55PowerCoefficients) i := by
  decide +kernel

theorem block55_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block55PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block55Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block55PowerCoefficients
      block55Margin0 (by norm_num) block55_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block55Margin1 : ℚ := (433229297137985166130960884119720849272394312827780604177235331185770868658689327 : ℚ) / 1000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block55_coefficient_bound_1 : ∀ i : Fin 37, block55Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block55PowerCoefficients) i := by
  decide +kernel

theorem block55_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block55PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block55Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block55PowerCoefficients
      block55Margin1 (by norm_num) block55_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block55Margin2 : ℚ := (13269833673656736939494738815177193681736403136197496919325371827038058251825452811966792587 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block55_coefficient_bound_2 : ∀ i : Fin 37, block55Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block55PowerCoefficients) i := by
  decide +kernel

theorem block55_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block55PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block55Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block55PowerCoefficients
      block55Margin2 (by norm_num) block55_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block55Margin3 : ℚ := (1311128170370567230231337575440616349921947510300307952508594654404882 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block55_coefficient_bound_3 : ∀ i : Fin 37, block55Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block55PowerCoefficients) i := by
  decide +kernel

theorem block55_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block55PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block55Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block55PowerCoefficients
      block55Margin3 (by norm_num) block55_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block55Margin4 : ℚ := (288092867101166044041201995448182929105404076489130522717366587323 : ℚ) / 4722366482869645213696

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block55_coefficient_bound_4 : ∀ i : Fin 37, block55Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block55PowerCoefficients) i := by
  decide +kernel

theorem block55_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block55PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block55Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block55PowerCoefficients
      block55Margin4 (by norm_num) block55_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block55Margin5 : ℚ := (36571189801999769137046352859848199010715771382148113138544484380852889 : ℚ) / 603669699812145076633600000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block55_coefficient_bound_5 : ∀ i : Fin 37, block55Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block55PowerCoefficients) i := by
  decide +kernel

theorem block55_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block55PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block55Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block55PowerCoefficients
      block55Margin5 (by norm_num) block55_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block55Margin6 : ℚ := (71936655874592192403414358934716236590550923309239849033966473910754732362118607 : ℚ) / 1000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block55_coefficient_bound_6 : ∀ i : Fin 37, block55Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block55PowerCoefficients) i := by
  decide +kernel

theorem block55_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block55PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block55Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block55PowerCoefficients
      block55Margin6 (by norm_num) block55_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block55Margin7 : ℚ := (7347982995979652691843367578155278992910967004050455479014311975780597441606743859283762427 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block55_coefficient_bound_7 : ∀ i : Fin 37, block55Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block55PowerCoefficients) i := by
  decide +kernel

theorem block55_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block55PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block55Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block55PowerCoefficients
      block55Margin7 (by norm_num) block55_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block55Margin8 : ℚ := (2342148727348115208252370306700926096592198761476202336176517472059392 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block55_coefficient_bound_8 : ∀ i : Fin 37, block55Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block55PowerCoefficients) i := by
  decide +kernel

theorem block55_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block55PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block55Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block55PowerCoefficients
      block55Margin8 (by norm_num) block55_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block55_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block55PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block55_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block55_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block55_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block55_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block55_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block55_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block55_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block55_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block55_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
