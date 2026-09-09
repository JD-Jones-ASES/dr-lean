import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (6,1). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block43PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-175173665185285352550238846436192000000000000000 : ℚ) / 7, (3272572669401894153505966734323080280000000000000 : ℚ) / 21, (-3829099635713445678350175807134199901500000000000 : ℚ) / 7, (25118556674825052357578501081343155640078125000000 : ℚ) / 21, (-31575615368390938557062319250306620487741796875000 : ℚ) / 21, (9632884106809099565468913237830263738652539062500 : ℚ) / 21, (14608573669142907971466665259619218512982714843750 : ℚ) / 7, (-29463879169231358293510880100156116547170458984375 : ℚ) / 7, (25018985438430091693777182299413981337355693359375 : ℚ) / 7, (-3275249736495491572172802611114086061772744140625 : ℚ) / 7, (-40400957648314530741536130690453800131641048828125 : ℚ) / 21, (35292260083270560614848651817865644603620002734375 : ℚ) / 21, (-3473165256623917842589613882040465756590487031250 : ℚ) / 21, (-6871034098929221784437194595642755267826306640625 : ℚ) / 14, (1606243273621552306553724382566559844039803468750 : ℚ) / 7, (507458735273047722526543298747549962921501578125 : ℚ) / 42, (-308868008698308710950480975655837324172877953125 : ℚ) / 7, (590051525896854975372082077922693531503719828125 : ℚ) / 42, (13310785845169642017939540525913219090200384375 : ℚ) / 7, (-31432350681728205733437026908688642352208884375 : ℚ) / 14, (7655376119518647201140740518399945194507255000 : ℚ) / 21, (2672235946550011875977680072977003367386988250 : ℚ) / 21, (-325786202863016675527999374869769426588680850 : ℚ) / 7, (2777730456250002939048885724682781351522625 : ℚ) / 7, (14323809329110499973324801079428993244076030 : ℚ) / 7, (-6154608771564593329347632505592610556095330 : ℚ) / 21, (-443784209983775990536462066574930898745450 : ℚ) / 21, (96158863808470755738999510982221772733800 : ℚ) / 7, (-3585813384507893774053357968232421437975 : ℚ) / 7, (-3239429938412430986776697694348547580935 : ℚ) / 21, (1021111967007724667219500152200281204645 : ℚ) / 21, (75393329228939028553625498121001368400 : ℚ) / 21, (-5001278348640564995050754065359891725 : ℚ) / 21, (402230225612279868322093101008395225 : ℚ) / 6, (280728604587982035268060995496470635 : ℚ) / 21, (22815398959447303219665734616320935 : ℚ) / 42]

def block43Margin0 : ℚ := (175701834813665529093487610659548216850184567443669046632190295992480675665174493682643345089 : ℚ) / 192414534860800000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block43_coefficient_bound_0 : ∀ i : Fin 37, block43Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block43PowerCoefficients) i := by
  decide +kernel

theorem block43_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block43PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block43Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block43PowerCoefficients
      block43Margin0 (by norm_num) block43_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block43Margin1 : ℚ := (1260645994090368578667043842463450839471008252597725688193722660771508749237729409 : ℚ) / 2800000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block43_coefficient_bound_1 : ∀ i : Fin 37, block43Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block43PowerCoefficients) i := by
  decide +kernel

theorem block43_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block43PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block43Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block43PowerCoefficients
      block43Margin1 (by norm_num) block43_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block43Margin2 : ℚ := (6646232778875419370907806752857844136930946758521645270915556364706678870583901831540140247 : ℚ) / 27487790694400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block43_coefficient_bound_2 : ∀ i : Fin 37, block43Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block43PowerCoefficients) i := by
  decide +kernel

theorem block43_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block43PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block43Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block43PowerCoefficients
      block43Margin2 (by norm_num) block43_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block43Margin3 : ℚ := (3427411749578040078298731958801807575172593185536524673328322349169097 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block43_coefficient_bound_3 : ∀ i : Fin 37, block43Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block43PowerCoefficients) i := by
  decide +kernel

theorem block43_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block43PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block43Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block43PowerCoefficients
      block43Margin3 (by norm_num) block43_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block43Margin4 : ℚ := (1623785542791166802841650877926045506696051704677581196934322691755656673817 : ℚ) / 10146682666745856000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block43_coefficient_bound_4 : ∀ i : Fin 37, block43Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block43PowerCoefficients) i := by
  decide +kernel

theorem block43_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block43PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block43Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block43PowerCoefficients
      block43Margin4 (by norm_num) block43_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block43Margin5 : ℚ := (1554685321253427335822965428175225871891884623866893398345965043315 : ℚ) / 9444732965739290427392

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block43_coefficient_bound_5 : ∀ i : Fin 37, block43Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block43PowerCoefficients) i := by
  decide +kernel

theorem block43_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block43PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block43Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block43PowerCoefficients
      block43Margin5 (by norm_num) block43_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block43Margin6 : ℚ := (557621902823447349608671660996696209264202864707106957126810607087289438251382969 : ℚ) / 2800000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block43_coefficient_bound_6 : ∀ i : Fin 37, block43Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block43PowerCoefficients) i := by
  decide +kernel

theorem block43_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block43PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block43Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block43PowerCoefficients
      block43Margin6 (by norm_num) block43_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block43Margin7 : ℚ := (7146508146991266448549850330819833075019332970503019167386579150493909704058475025546906087 : ℚ) / 27487790694400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block43_coefficient_bound_7 : ∀ i : Fin 37, block43Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block43PowerCoefficients) i := by
  decide +kernel

theorem block43_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block43PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block43Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block43PowerCoefficients
      block43Margin7 (by norm_num) block43_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block43Margin8 : ℚ := (7087010497167179388432214462837295969041980533858287604143874647160832 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block43_coefficient_bound_8 : ∀ i : Fin 37, block43Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block43PowerCoefficients) i := by
  decide +kernel

theorem block43_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block43PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block43Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block43PowerCoefficients
      block43Margin8 (by norm_num) block43_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block43_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block43PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block43_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block43_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block43_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block43_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block43_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block43_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block43_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block43_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block43_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
