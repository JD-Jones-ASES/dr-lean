import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (4,6). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block34PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-150590211862272159079959668814720000000000000000 : ℚ) / 7, (888195930692017251316627528825527800000000000000 : ℚ) / 7, (-3030131276998470455148650487801354112600000000000 : ℚ) / 7, (6764401770078134687895340109953529934200000000000 : ℚ) / 7, (-9906258779352722553379490140305666046751250000000 : ℚ) / 7, (9298378423137241083476731486428802359508750000000 : ℚ) / 7, (-5126742862818862281900117437169354377338750000000 : ℚ) / 7, (3401194707249219923492497202940458489983750000000 : ℚ) / 7, (-7235150473629380278286557018758573063547234375000 : ℚ) / 7, (11059124761109470635765130680247581740705796875000 : ℚ) / 7, (-6661065852522008214875129800220319537448503125000 : ℚ) / 7, (-1977505089785354863575129892237505717673728125000 : ℚ) / 7, (5435515537322078302529881488088286153346669125000 : ℚ) / 7, (-2141973334183377558538428031375578973243837625000 : ℚ) / 7, (-821762923382880445714145643543960238115527425000 : ℚ) / 7, (691819578938537561970347012038148345372541975000 : ℚ) / 7, (-171508792351029415795579918153587632587929650000 : ℚ) / 7, (-51786620298145482933675722425916318583335825000 : ℚ) / 7, (58096566666980834280133386934264304083235166250 : ℚ) / 7, (-6355262348105507622126554473732731116182763750 : ℚ) / 7, (-3691181275432114129367641628592397073649516000 : ℚ) / 7, (2018324962986650537352521324702294580672289500 : ℚ) / 7, (-35921909203885324417813623172045362320883890 : ℚ) / 7, (-131051107966597842123498888920484945785821120 : ℚ) / 7, (20917204581319781038030516253685644187162652 : ℚ) / 7, (1627889024001460985762386951583470982142536 : ℚ) / 7, (-1221893766823921372736990063065542417163360 : ℚ) / 7, (103221432583305267055691145930900488814270 : ℚ) / 7, (22775709879900011822696372944174950663290 : ℚ) / 7, (-5398040866265518541241347082340633436218 : ℚ) / 7, (-5400244936363527750721293511075868662 : ℚ) / 1, (99908180828294615675974839548014332370 : ℚ) / 7, (-5817028488934929994959928598401649280 : ℚ) / 7, (-952710418312760614460661771089698050 : ℚ) / 7, (101578124062930602160598748900489728 : ℚ) / 7, (9126159583778921287866293846528374 : ℚ) / 7]

def block34Margin0 : ℚ := (247548400776489624929409606082629196910442129016503889737027679983541689797411310391590631467 : ℚ) / 240518168576000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block34_coefficient_bound_0 : ∀ i : Fin 37, block34Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block34PowerCoefficients) i := by
  decide +kernel

theorem block34_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block34PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block34Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block34PowerCoefficients
      block34Margin0 (by norm_num) block34_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block34Margin1 : ℚ := (2116034303433152239891558841165755814025726437138934042197152560602533565587320327 : ℚ) / 3500000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block34_coefficient_bound_1 : ∀ i : Fin 37, block34Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block34PowerCoefficients) i := by
  decide +kernel

theorem block34_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block34PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block34Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block34PowerCoefficients
      block34Margin1 (by norm_num) block34_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block34Margin2 : ℚ := (13706012982082520198024558862003906968683954538245665031655624235734508752053952763782260941 : ℚ) / 34359738368000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block34_coefficient_bound_2 : ∀ i : Fin 37, block34Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block34PowerCoefficients) i := by
  decide +kernel

theorem block34_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block34PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block34Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block34PowerCoefficients
      block34Margin2 (by norm_num) block34_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block34Margin3 : ℚ := (32164446079466346170188846721918817189717842912725134511538482625365764 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block34_coefficient_bound_3 : ∀ i : Fin 37, block34Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block34PowerCoefficients) i := by
  decide +kernel

theorem block34_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block34PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block34Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block34PowerCoefficients
      block34Margin3 (by norm_num) block34_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block34Margin4 : ℚ := (696533167665349270331531518981716914477460062578413188603297812860743228901 : ℚ) / 2318660535228167094272000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block34_coefficient_bound_4 : ∀ i : Fin 37, block34Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block34PowerCoefficients) i := by
  decide +kernel

theorem block34_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block34PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block34Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block34PowerCoefficients
      block34Margin4 (by norm_num) block34_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block34Margin5 : ℚ := (712314176139896401059704756312074035376191460349995328236796131389 : ℚ) / 2361183241434822606848

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block34_coefficient_bound_5 : ∀ i : Fin 37, block34Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block34PowerCoefficients) i := by
  decide +kernel

theorem block34_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block34PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block34Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block34PowerCoefficients
      block34Margin5 (by norm_num) block34_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block34Margin6 : ℚ := (165056523327583814942652800673971981118536731719290275943262944136411688732290801 : ℚ) / 500000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block34_coefficient_bound_6 : ∀ i : Fin 37, block34Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block34PowerCoefficients) i := by
  decide +kernel

theorem block34_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block34PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block34Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block34PowerCoefficients
      block34Margin6 (by norm_num) block34_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block34Margin7 : ℚ := (13459050082005138529245643236932970162648017585976627955953723159397457604877021724709404061 : ℚ) / 34359738368000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block34_coefficient_bound_7 : ∀ i : Fin 37, block34Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block34PowerCoefficients) i := by
  decide +kernel

theorem block34_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block34PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block34Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block34PowerCoefficients
      block34Margin7 (by norm_num) block34_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block34Margin8 : ℚ := (49834025745507509963069515229321503353382386930168265934546930871926784 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block34_coefficient_bound_8 : ∀ i : Fin 37, block34Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block34PowerCoefficients) i := by
  decide +kernel

theorem block34_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block34PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block34Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block34PowerCoefficients
      block34Margin8 (by norm_num) block34_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block34_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block34PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block34_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block34_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block34_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block34_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block34_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block34_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block34_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block34_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block34_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
