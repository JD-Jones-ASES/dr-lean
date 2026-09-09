import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (3,0). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block21PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-158008458342819635766407033678784000000000000000 : ℚ) / 7, (956821978839679919569276941135939960000000000000 : ℚ) / 7, (-3297868677776122898968061298754121543800000000000 : ℚ) / 7, (7111052802648400419935456138237866969500000000000 : ℚ) / 7, (-8771968096501714629966333739220695767360000000000 : ℚ) / 7, (2482298667702516381355681700962307654700000000000 : ℚ) / 7, (12239184583272048716749019126420187025215000000000 : ℚ) / 7, (-23836156267282685635220471176660703136600000000000 : ℚ) / 7, (19415736892639159930086822649419487903121500000000 : ℚ) / 7, (-1640033693937466746796716129161130955276250000000 : ℚ) / 7, (-10883618517181033251858610146900134468236400000000 : ℚ) / 7, (8668877763696968732192454112339387729872150000000 : ℚ) / 7, (-285272252763131136876523070866495222168142000000 : ℚ) / 7, (-375552829539233173638820860957345313371710000000 : ℚ) / 1, (1014341932805696206452359043086102661749619100000 : ℚ) / 7, (142628365333166542704744772505545376304386750000 : ℚ) / 7, (-191100529616057599044261968957763705677256950000 : ℚ) / 7, (52792845945669300475596629062990182737219000000 : ℚ) / 7, (851241028432765316111535358854616334713840000 : ℚ) / 1, (-9433989310334251903927505993979716606120850000 : ℚ) / 7, (1903799096094353488515378262303575658363992000 : ℚ) / 7, (578354141998976333316819362421977787009734000 : ℚ) / 7, (-207654190549767084222187755806286552617916320 : ℚ) / 7, (-4040518038914996685539217241845423535847200 : ℚ) / 7, (6961639491763644974446629591606167038836576 : ℚ) / 7, (-1140125576299530148308266795012654419696520 : ℚ) / 7, (-75429614157692761179109157158153945704420 : ℚ) / 7, (38026750066801048584257564656699287977470 : ℚ) / 7, (-3520489291247359503000178635921659923390 : ℚ) / 7, (-597446058455263422117102556832416027514 : ℚ) / 7, (92254849194492092535965298636999738690 : ℚ) / 7, (-156601244532735706827183651231681380 : ℚ) / 1, (-1443400127079905084038010421053255310 : ℚ) / 7, (43646850183290493115882274918179180 : ℚ) / 7, (9126159583778921287866293846528374 : ℚ) / 7, (0 : ℚ) / 1]

def block21Margin0 : ℚ := (11981617686302401536404877742821558515409506214135680368879273297862076218628022989768153987 : ℚ) / 12025908428800000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block21_coefficient_bound_0 : ∀ i : Fin 37, block21Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block21PowerCoefficients) i := by
  decide +kernel

theorem block21_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block21PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block21Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block21PowerCoefficients
      block21Margin0 (by norm_num) block21_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block21Margin1 : ℚ := (197472426894635353289383503497075135405730936504378973354793831173747679939314587 : ℚ) / 350000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block21_coefficient_bound_1 : ∀ i : Fin 37, block21Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block21PowerCoefficients) i := by
  decide +kernel

theorem block21_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block21PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block21Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block21PowerCoefficients
      block21Margin1 (by norm_num) block21_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block21Margin2 : ℚ := (620351632342452538039593846946009233249336523941032274560788714128620426085059446694294487 : ℚ) / 1717986918400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block21_coefficient_bound_2 : ∀ i : Fin 37, block21Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block21PowerCoefficients) i := by
  decide +kernel

theorem block21_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block21PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block21Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block21PowerCoefficients
      block21Margin2 (by norm_num) block21_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block21Margin3 : ℚ := (5751081123267740055454006711343539330911263871545368616029032080221524 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block21_coefficient_bound_3 : ∀ i : Fin 37, block21Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block21PowerCoefficients) i := by
  decide +kernel

theorem block21_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block21PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block21Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block21PowerCoefficients
      block21Margin3 (by norm_num) block21_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block21Margin4 : ℚ := (48727195330961556367249662799652750142957937387943377184861922203310586213 : ℚ) / 181145354314700554240000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block21_coefficient_bound_4 : ∀ i : Fin 37, block21Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block21PowerCoefficients) i := by
  decide +kernel

theorem block21_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block21PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block21Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block21PowerCoefficients
      block21Margin4 (by norm_num) block21_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block21Margin5 : ℚ := (1118053354524411282300950492140034782421996541863252930231784848547 : ℚ) / 4132070672510939561984

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block21_coefficient_bound_5 : ∀ i : Fin 37, block21Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block21PowerCoefficients) i := by
  decide +kernel

theorem block21_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block21PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block21Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block21PowerCoefficients
      block21Margin5 (by norm_num) block21_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block21Margin6 : ℚ := (104288189503539359522088755701621497771894223276071001970738989487848759117723809 : ℚ) / 350000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block21_coefficient_bound_6 : ∀ i : Fin 37, block21Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block21PowerCoefficients) i := by
  decide +kernel

theorem block21_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block21PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block21Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block21PowerCoefficients
      block21Margin6 (by norm_num) block21_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block21Margin7 : ℚ := (608899721002537258555854677124144870787547468136354169018816984569932568981653824683195363 : ℚ) / 1717986918400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block21_coefficient_bound_7 : ∀ i : Fin 37, block21Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block21PowerCoefficients) i := by
  decide +kernel

theorem block21_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block21PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block21Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block21PowerCoefficients
      block21Margin7 (by norm_num) block21_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block21Margin8 : ℚ := (9002878586219118838770379043212617119027806050565196836369045581791232 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block21_coefficient_bound_8 : ∀ i : Fin 37, block21Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block21PowerCoefficients) i := by
  decide +kernel

theorem block21_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block21PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block21Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block21PowerCoefficients
      block21Margin8 (by norm_num) block21_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block21_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block21PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block21_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block21_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block21_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block21_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block21_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block21_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block21_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block21_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block21_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
