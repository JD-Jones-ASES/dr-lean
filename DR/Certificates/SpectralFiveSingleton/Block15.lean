import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (2,1). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block15PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-149194962235793169635076907281248000000000000000 : ℚ) / 7, (2646353475507708934224327790799473640000000000000 : ℚ) / 21, (-2983392596237030495181444243101880112100000000000 : ℚ) / 7, (57026905619920831217627997930131895981050000000000 : ℚ) / 63, (-69503971920994257271550441273670432185080000000000 : ℚ) / 63, (7033219545122759138874776038422749971670000000000 : ℚ) / 21, (1386718560473306536251141698442815203827500000000 : ℚ) / 1, (-2615136031662382373778908073286312678780000000000 : ℚ) / 1, (40608435169441762537713368468490687892027750000000 : ℚ) / 21, (8096531586837253338076181132462279934651625000000 : ℚ) / 63, (-83748922705033184755865541404488675864716700000000 : ℚ) / 63, (17745692222644343228020702359490124888685275000000 : ℚ) / 21, (1081638766099289313064237569456458320896907000000 : ℚ) / 9, (-19643292614972952799517536117385344748123668000000 : ℚ) / 63, (507561934492234973869945972940791320488178450000 : ℚ) / 7, (2019960318253874969707773928499073348759551275000 : ℚ) / 63, (-396650127321293404945100055611435046268954825000 : ℚ) / 21, (65685433049416459260691615375233874271353400000 : ℚ) / 21, (82270452699322710301632795896399518059218390000 : ℚ) / 63, (-19234539389677096068820829330112785960725985000 : ℚ) / 21, (2352634440969315398974886927319523000283842000 : ℚ) / 21, (606425296818589107244083767808409249107511500 : ℚ) / 7, (-1030336223968784914995323494663673798378729960 : ℚ) / 63, (-60127799237705065903228057713434273493880760 : ℚ) / 21, (15461089024140570278119107372494041131531176 : ℚ) / 21, (-2054227510923901565530655464205399497571416 : ℚ) / 63, (-1274619954009210426123544189719993242209390 : ℚ) / 63, (65412048278253461198611590439609980248185 : ℚ) / 21, (1161667005080748990656828496226540652755 : ℚ) / 9, (-1898783158201651891972490076647541551159 : ℚ) / 21, (8422383950447796757294476403784630931 : ℚ) / 7, (50664207557540519299447507954193941630 : ℚ) / 63, (-2677335821778980703038614545659223115 : ℚ) / 21, (-1959309854669211992089388388179940125 : ℚ) / 126, (8530975263097687290831535552189567 : ℚ) / 63, (4563079791889460643933146923264187 : ℚ) / 126]

def block15Margin0 : ℚ := (427803790553291364079470295105870739791859289623898044345755914690858173654103121007515070327 : ℚ) / 412316860416000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block15_coefficient_bound_0 : ∀ i : Fin 37, block15Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block15PowerCoefficients) i := by
  decide +kernel

theorem block15_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block15PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block15Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block15PowerCoefficients
      block15Margin0 (by norm_num) block15_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block15Margin1 : ℚ := (8661822650535592111562830509675952982346381524776357583295582354293115198765417003 : ℚ) / 14000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block15_coefficient_bound_1 : ∀ i : Fin 37, block15Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block15PowerCoefficients) i := by
  decide +kernel

theorem block15_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block15PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block15Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block15PowerCoefficients
      block15Margin1 (by norm_num) block15_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block15Margin2 : ℚ := (57193597802619975826153940806333557685178216063201618464527156172917173822227055118842245149 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block15_coefficient_bound_2 : ∀ i : Fin 37, block15Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block15PowerCoefficients) i := by
  decide +kernel

theorem block15_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block15PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block15Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block15PowerCoefficients
      block15Margin2 (by norm_num) block15_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block15Margin3 : ℚ := (33946708669068560901639416614587585774274214898784948342196531062243499 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block15_coefficient_bound_3 : ∀ i : Fin 37, block15Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block15PowerCoefficients) i := by
  decide +kernel

theorem block15_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block15PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block15Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block15PowerCoefficients
      block15Margin3 (by norm_num) block15_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block15Margin4 : ℚ := (1617709713759647740431365677330815785199668999441513824824700263461261299 : ℚ) / 5117043939813886001152000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block15_coefficient_bound_4 : ∀ i : Fin 37, block15Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block15PowerCoefficients) i := by
  decide +kernel

theorem block15_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block15PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block15Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block15PowerCoefficients
      block15Margin4 (by norm_num) block15_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block15Margin5 : ℚ := (2991179033547433911954588072417920683231070571783383215872070850781 : ℚ) / 9444732965739290427392

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block15_coefficient_bound_5 : ∀ i : Fin 37, block15Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block15PowerCoefficients) i := by
  decide +kernel

theorem block15_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block15PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block15Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block15PowerCoefficients
      block15Margin5 (by norm_num) block15_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block15Margin6 : ℚ := (4762232507376814139860892601707799799245673931186868106922048464773119168718792723 : ℚ) / 14000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block15_coefficient_bound_6 : ∀ i : Fin 37, block15Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block15PowerCoefficients) i := by
  decide +kernel

theorem block15_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block15PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block15Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block15PowerCoefficients
      block15Margin6 (by norm_num) block15_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block15Margin7 : ℚ := (162551690212564030607680939704444967197717005306807962585222738773081125674226231083721942887 : ℚ) / 412316860416000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block15_coefficient_bound_7 : ∀ i : Fin 37, block15Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block15PowerCoefficients) i := by
  decide +kernel

theorem block15_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block15PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block15Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block15PowerCoefficients
      block15Margin7 (by norm_num) block15_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block15Margin8 : ℚ := (7002382737465173770986920372487444707342799206968842858673231510536192 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block15_coefficient_bound_8 : ∀ i : Fin 37, block15Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block15PowerCoefficients) i := by
  decide +kernel

theorem block15_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block15PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block15Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block15PowerCoefficients
      block15Margin8 (by norm_num) block15_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block15_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block15PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block15_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block15_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block15_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block15_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block15_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block15_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block15_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block15_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block15_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
