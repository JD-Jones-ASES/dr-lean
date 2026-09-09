import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (3,4). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block25PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-148733176864205954156248467243584000000000000000 : ℚ) / 7, (2644672994946533977469578141525285880000000000000 : ℚ) / 21, (-2996739595307896545096204746268273848800000000000 : ℚ) / 7, (19564609365166217393375610625520364933059375000000 : ℚ) / 21, (-8701627995324236818786487454780561175606093750000 : ℚ) / 7, (2353812682529861917810365765988680737501640625000 : ℚ) / 3, (9011019620637858239415042932021180018406523437500 : ℚ) / 21, (-25597530217641889847133657300528587142312050781250 : ℚ) / 21, (4315198378646161354335439900504014977442496093750 : ℚ) / 7, (15678790197805485271936308533026566890928003906250 : ℚ) / 21, (-23533433217310618297193249282199653500904883593750 : ℚ) / 21, (326469244276851093418996641345656186822389843750 : ℚ) / 1, (405814873905237518078336049852359515137562750000 : ℚ) / 1, (-6117209569044155804432653160299517454329540281250 : ℚ) / 21, (-114080382072930136622264631364189468613269337500 : ℚ) / 7, (1288250950056783749991061084675325424042982475000 : ℚ) / 21, (-17757786295189773777328172087433998527342881250 : ℚ) / 1, (-13519324651626556556826503247410502479827587500 : ℚ) / 7, (83982048050413384233587670165909739274090108750 : ℚ) / 21, (-5416688355045156115133776223115048806943765000 : ℚ) / 7, (-1230615130968047320782486372589478109486083000 : ℚ) / 7, (3375637470172204655978168611805290507678506500 : ℚ) / 21, (-162591279680383488045364272424284750081327460 : ℚ) / 21, (-209892902942895748519480302794141366980164170 : ℚ) / 21, (27242294620475153459541043062271947982885028 : ℚ) / 21, (878465966080513517795463858113074646593172 : ℚ) / 7, (-1651953439607930562207880480669418117119780 : ℚ) / 21, (34127472863298652848954808284306076563080 : ℚ) / 7, (10366713751830049147904360648718350795350 : ℚ) / 7, (-2225746123894136773666696729031838989894 : ℚ) / 7, (-237229545341267950575094462478354757694 : ℚ) / 21, (5392309150901293486996569840668378260 : ℚ) / 1, (-6471200204980016392702436622991920590 : ℚ) / 21, (-70632873846134463268156590377067870 : ℚ) / 1, (71025328934627256979481156457764302 : ℚ) / 21, (9126159583778921287866293846528374 : ℚ) / 21]

def block25Margin0 : ℚ := (250270895380612862276752831640153139444927485517714304425593786087160462412750700059158631069 : ℚ) / 240518168576000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block25_coefficient_bound_0 : ∀ i : Fin 37, block25Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block25PowerCoefficients) i := by
  decide +kernel

theorem block25_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block25PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block25Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block25PowerCoefficients
      block25Margin0 (by norm_num) block25_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block25Margin1 : ℚ := (2184719711282669708197716414970175607935228437678033561797998779665717325524042399 : ℚ) / 3500000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block25_coefficient_bound_1 : ∀ i : Fin 37, block25Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block25PowerCoefficients) i := by
  decide +kernel

theorem block25_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block25PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block25Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block25PowerCoefficients
      block25Margin1 (by norm_num) block25_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block25Margin2 : ℚ := (14581233298802957670802551085768928673675886824834129018645044193629257181125106815816684227 : ℚ) / 34359738368000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block25_coefficient_bound_2 : ∀ i : Fin 37, block25Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block25PowerCoefficients) i := by
  decide +kernel

theorem block25_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block25PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block25Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block25PowerCoefficients
      block25Margin2 (by norm_num) block25_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block25Margin3 : ℚ := (35149630601975415830836069684830860182656449111148682754979763551223128 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block25_coefficient_bound_3 : ∀ i : Fin 37, block25Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block25PowerCoefficients) i := by
  decide +kernel

theorem block25_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block25PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block25Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block25PowerCoefficients
      block25Margin3 (by norm_num) block25_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block25Margin4 : ℚ := (3243665685573808257477743006139963362906711155423184810560617947944158962863 : ℚ) / 9781849132993829928960000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block25_coefficient_bound_4 : ∀ i : Fin 37, block25Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block25PowerCoefficients) i := by
  decide +kernel

theorem block25_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block25PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block25Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block25PowerCoefficients
      block25Margin4 (by norm_num) block25_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block25Margin5 : ℚ := (5510762645816683506406207192297655397324723744417785943981310697037 : ℚ) / 16528282690043758247936

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block25_coefficient_bound_5 : ∀ i : Fin 37, block25Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block25PowerCoefficients) i := by
  decide +kernel

theorem block25_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block25PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block25Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block25PowerCoefficients
      block25Margin5 (by norm_num) block25_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block25Margin6 : ℚ := (1272609307997823862810305139932822193539926058841788948761504724152270556095086899 : ℚ) / 3500000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block25_coefficient_bound_6 : ∀ i : Fin 37, block25Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block25PowerCoefficients) i := by
  decide +kernel

theorem block25_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block25PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block25Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block25PowerCoefficients
      block25Margin6 (by norm_num) block25_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block25Margin7 : ℚ := (14673418711261754473259609778356244456638318685765958401804554448342023637721483903447863107 : ℚ) / 34359738368000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block25_coefficient_bound_7 : ∀ i : Fin 37, block25Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block25PowerCoefficients) i := by
  decide +kernel

theorem block25_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block25PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block25Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block25PowerCoefficients
      block25Margin7 (by norm_num) block25_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block25Margin8 : ℚ := (53726344301446797338174336581036242625140315397385653992638704419483648 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block25_coefficient_bound_8 : ∀ i : Fin 37, block25Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block25PowerCoefficients) i := by
  decide +kernel

theorem block25_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block25PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block25Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block25PowerCoefficients
      block25Margin8 (by norm_num) block25_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block25_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block25PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block25_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block25_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block25_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block25_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block25_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block25_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block25_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block25_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block25_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
