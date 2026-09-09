import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (6,2). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block44PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-172854844815631932147699204827392000000000000000 : ℚ) / 7, (3178753254820368757096464646238707280000000000000 : ℚ) / 21, (-10984012230693596685556038039075896827000000000000 : ℚ) / 21, (7864787083385627902439494982481541289640625000000 : ℚ) / 7, (-28901682604665311407011537789969885667583593750000 : ℚ) / 21, (2577385674157843464130575160664959471782031250000 : ℚ) / 7, (40762245651393071929602465518869318208133203125000 : ℚ) / 21, (-77663485564371320226422018953301430519429882812500 : ℚ) / 21, (60348847343968308762541193184440391935229384765625 : ℚ) / 21, (77963531945974234561031493940106430464013671875 : ℚ) / 21, (-1925602212090739636293099000207596002684251953125 : ℚ) / 1, (9818575879674774248324328326148726666806644140625 : ℚ) / 7, (732127380275616254686462708140760405513028984375 : ℚ) / 21, (-3512796519067164607664726303801878558546177656250 : ℚ) / 7, (3620202665925968628931073460904022630103194078125 : ℚ) / 21, (739024494485290028671808989500550290947179156250 : ℚ) / 21, (-915464594111658174397116026058562627635479875000 : ℚ) / 21, (70465074258790353527453558352492425941610890625 : ℚ) / 7, (75034266859623750904841251536843484348720981250 : ℚ) / 21, (-14977978614753348754794150916381688656967265625 : ℚ) / 7, (1018947249509409417179734594891027901205135000 : ℚ) / 7, (3527548859027296232939754968484473782849934500 : ℚ) / 21, (-113112982117109341846991481884235274299059150 : ℚ) / 3, (-23732853921057486843224457368608527731007300 : ℚ) / 7, (50793547814911102936909291053915268815611540 : ℚ) / 21, (-3904503726281213990586124418825920776785360 : ℚ) / 21, (-1172678147280446559159629557974039672638600 : ℚ) / 21, (109780433783185212031944250768342777913250 : ℚ) / 7, (9175782450650941385876209952181320551225 : ℚ) / 21, (-6347237545419357408938815408904884437785 : ℚ) / 21, (332375203590528958866011815867304789855 : ℚ) / 7, (54178411457723967698062473078089647775 : ℚ) / 7, (-7694054889893738110703367831357574300 : ℚ) / 21, (947218070778055383569748652126470025 : ℚ) / 21, (424564815419280251218127583295015660 : ℚ) / 21, (22815398959447303219665734616320935 : ℚ) / 21]

def block44Margin0 : ℚ := (88618115550458272603787177994684490274585227564130017540106899074061968926277067863587349609 : ℚ) / 96207267430400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block44_coefficient_bound_0 : ∀ i : Fin 37, block44Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block44PowerCoefficients) i := by
  decide +kernel

theorem block44_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block44PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block44Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block44PowerCoefficients
      block44Margin0 (by norm_num) block44_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block44Margin1 : ℚ := (639185991050076905345815377736473475084867770145720516100473296024031093232928669 : ℚ) / 1400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block44_coefficient_bound_1 : ∀ i : Fin 37, block44Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block44PowerCoefficients) i := by
  decide +kernel

theorem block44_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block44PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block44Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block44PowerCoefficients
      block44Margin1 (by norm_num) block44_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block44Margin2 : ℚ := (3347926399955302357199501128145326232448508085008740018373566550350570737114633265763348767 : ℚ) / 13743895347200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block44_coefficient_bound_2 : ∀ i : Fin 37, block44Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block44PowerCoefficients) i := by
  decide +kernel

theorem block44_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block44PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block44Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block44PowerCoefficients
      block44Margin2 (by norm_num) block44_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block44Margin3 : ℚ := (3370971862611190363171553612468062050284799914594809982162303071972074 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block44_coefficient_bound_3 : ∀ i : Fin 37, block44Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block44PowerCoefficients) i := by
  decide +kernel

theorem block44_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block44PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block44Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block44PowerCoefficients
      block44Margin3 (by norm_num) block44_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block44Margin4 : ℚ := (28584787859385551318594371853943726683225307671867461007222063100646509839 : ℚ) / 184485139395379200000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block44_coefficient_bound_4 : ∀ i : Fin 37, block44Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block44PowerCoefficients) i := by
  decide +kernel

theorem block44_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block44PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block44Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block44PowerCoefficients
      block44Margin4 (by norm_num) block44_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block44Margin5 : ℚ := (5224715329539231108043911284376850391924173370803777718549875426125 : ℚ) / 33056565380087516495872

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block44_coefficient_bound_5 : ∀ i : Fin 37, block44Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block44PowerCoefficients) i := by
  decide +kernel

theorem block44_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block44PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block44Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block44PowerCoefficients
      block44Margin5 (by norm_num) block44_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block44Margin6 : ℚ := (265365958853966916784521472297678526338818385470027198163880694393072675940485789 : ℚ) / 1400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block44_coefficient_bound_6 : ∀ i : Fin 37, block44Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block44PowerCoefficients) i := by
  decide +kernel

theorem block44_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block44PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block44Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block44PowerCoefficients
      block44Margin6 (by norm_num) block44_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block44Margin7 : ℚ := (3403906556786603611229897225488823053979965164515791988682233664743572905965318472161439567 : ℚ) / 13743895347200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block44_coefficient_bound_7 : ∀ i : Fin 37, block44Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block44PowerCoefficients) i := by
  decide +kernel

theorem block44_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block44PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block44Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block44PowerCoefficients
      block44Margin7 (by norm_num) block44_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block44Margin8 : ℚ := (6776195674465245092901611589271113203038557553352249772149419102101504 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block44_coefficient_bound_8 : ∀ i : Fin 37, block44Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block44PowerCoefficients) i := by
  decide +kernel

theorem block44_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block44PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block44Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block44PowerCoefficients
      block44Margin8 (by norm_num) block44_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block44_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block44PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block44_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block44_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block44_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block44_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block44_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block44_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block44_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block44_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block44_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
