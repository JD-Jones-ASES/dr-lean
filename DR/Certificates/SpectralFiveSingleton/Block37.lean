import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (5,2). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block37PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-166360169078258886418908720038656000000000000000 : ℚ) / 7, (3036596883824103881559106113376488200000000000000 : ℚ) / 21, (-10445768740002435320038823252091026213000000000000 : ℚ) / 21, (9603535946760805450001958729121803081359375000000 : ℚ) / 9, (-27526383971272095234842954473277427869185937500000 : ℚ) / 21, (24071943775033440990491119502299271716524218750000 : ℚ) / 63, (109887626837793496470594797734649127815545703125000 : ℚ) / 63, (-210035474456737760091140196002281319511717968750000 : ℚ) / 63, (160481989462014320117068626280105205064453593750000 : ℚ) / 63, (4865076194166078918988461239993607495631718750000 : ℚ) / 63, (-36857390492659268543196569957115590145235562500000 : ℚ) / 21, (76809288642821041089861403342745623890706023437500 : ℚ) / 63, (5082653800143847586851583356079362742586724375000 : ℚ) / 63, (-28326430170347083841882139688386810575149685000000 : ℚ) / 63, (1236720186456778432322491010887988685438520250000 : ℚ) / 9, (2401260349472181156144609618536749153705957375000 : ℚ) / 63, (-752833236076517733300097220394246873249136375000 : ℚ) / 21, (151582133718342434852663542161243014124019250000 : ℚ) / 21, (183368506621668017797327163590632964434840462500 : ℚ) / 63, (-12084079744863755689083817485065495701624525000 : ℚ) / 7, (8462651364141096665168910663820185130796785000 : ℚ) / 63, (9227677999398403731492174745604689421546650000 : ℚ) / 63, (-671222636688258179469185765449701169994935700 : ℚ) / 21, (-249411931588040215383871582035574766050503850 : ℚ) / 63, (13119462431465845932229921044618394042198420 : ℚ) / 7, (-141590134768978024209941249964470242490940 : ℚ) / 1, (-3233998718798901196788876820545616302210700 : ℚ) / 63, (706087890835550010701988479729822439899750 : ℚ) / 63, (6037469892618868503025719548177714413300 : ℚ) / 21, (-2520430176964638046828591600749361463660 : ℚ) / 9, (1688396782522372846866955833039436557380 : ℚ) / 63, (324388391824180950383661923076451610900 : ℚ) / 63, (-2846438169797673790488690940826510900 : ℚ) / 7, (365356828186005415293760529619087850 : ℚ) / 63, (789611198770437102732779337156150620 : ℚ) / 63, (45630797918894606439331469232641870 : ℚ) / 63]

def block37Margin0 : ℚ := (137593975352669166784503493107258206326098389829981437263907333909305075722122657251496199809 : ℚ) / 144310901145600000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block37_coefficient_bound_0 : ∀ i : Fin 37, block37Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block37PowerCoefficients) i := by
  decide +kernel

theorem block37_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block37PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block37Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block37PowerCoefficients
      block37Margin0 (by norm_num) block37_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block37Margin1 : ℚ := (50228393580976954854974071067287833055499931389684735992512635730351644070367989 : ℚ) / 100000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block37_coefficient_bound_1 : ∀ i : Fin 37, block37Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block37PowerCoefficients) i := by
  decide +kernel

theorem block37_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block37PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block37Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block37PowerCoefficients
      block37Margin1 (by norm_num) block37_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block37Margin2 : ℚ := (2015138098862047385341174738139524803907462070869249724329905951351734618337615886879960989 : ℚ) / 6871947673600000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block37_coefficient_bound_2 : ∀ i : Fin 37, block37Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block37PowerCoefficients) i := by
  decide +kernel

theorem block37_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block37PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block37Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block37PowerCoefficients
      block37Margin2 (by norm_num) block37_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block37Margin3 : ℚ := (4380764158642192391755549975981615165365418582456547411832653123230916 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block37_coefficient_bound_3 : ∀ i : Fin 37, block37Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block37PowerCoefficients) i := by
  decide +kernel

theorem block37_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block37PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block37Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block37PowerCoefficients
      block37Margin3 (by norm_num) block37_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block37Margin4 : ℚ := (6371547877591930788110432297226680298202809874545724035078239767320673485023 : ℚ) / 31263012143801303040000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block37_coefficient_bound_4 : ∀ i : Fin 37, block37Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block37PowerCoefficients) i := by
  decide +kernel

theorem block37_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block37PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block37Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block37PowerCoefficients
      block37Margin4 (by norm_num) block37_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block37Margin5 : ℚ := (3413439232623659886733332734450726210394145548420409514465487360375 : ℚ) / 16528282690043758247936

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block37_coefficient_bound_5 : ∀ i : Fin 37, block37Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block37PowerCoefficients) i := by
  decide +kernel

theorem block37_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block37PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block37Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block37PowerCoefficients
      block37Margin5 (by norm_num) block37_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block37Margin6 : ℚ := (166274322955233800916360619905047661985268038056263127028204293192975786499487163 : ℚ) / 700000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block37_coefficient_bound_6 : ∀ i : Fin 37, block37Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block37PowerCoefficients) i := by
  decide +kernel

theorem block37_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block37PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block37Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block37PowerCoefficients
      block37Margin6 (by norm_num) block37_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block37Margin7 : ℚ := (6119366746415061893289944186208934254969497654885013840655227921539418020455958337856491367 : ℚ) / 20615843020800000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block37_coefficient_bound_7 : ∀ i : Fin 37, block37Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block37PowerCoefficients) i := by
  decide +kernel

theorem block37_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block37PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block37Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block37PowerCoefficients
      block37Margin7 (by norm_num) block37_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block37Margin8 : ℚ := (7855210864012923151115322531896978302262286444091964180943213797031936 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block37_coefficient_bound_8 : ∀ i : Fin 37, block37Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block37PowerCoefficients) i := by
  decide +kernel

theorem block37_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block37PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block37Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block37PowerCoefficients
      block37Margin8 (by norm_num) block37_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block37_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block37PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block37_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block37_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block37_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block37_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block37_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block37_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block37_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block37_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block37_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
