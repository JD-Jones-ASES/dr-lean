import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (0,5). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block05PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-18132904183204770938191053038368000000000000000 : ℚ) / 1, (322357804323988609775584557472550000000000000000 : ℚ) / 3, (-1119902671170079492109987289781425362500000000000 : ℚ) / 3, (864453165813993351856287685120626037109375000000 : ℚ) / 1, (-3968216434951207803928995690604006224072265625000 : ℚ) / 3, (1313129059914348452061902617380498393432617187500 : ℚ) / 1, (-2059757728595052206742565386944899056000976562500 : ℚ) / 3, (278403061799549134803051225027607118725585937500 : ℚ) / 3, (-193900203241204929849969316785689684436523437500 : ℚ) / 3, (406377641147482231498232774822550419075195312500 : ℚ) / 1, (-827236675495711197803748230032273184871718750000 : ℚ) / 3, (-379703104493213850662404766925323837341308593750 : ℚ) / 3, (305960759133323235812123099530468754508812500000 : ℚ) / 1, (-142145193522254774898861077533950015689511718750 : ℚ) / 3, (-191618135009506193860863492751742474534710937500 : ℚ) / 3, (100864573533002431959103674352896522952832031250 : ℚ) / 3, (1996243354047448768878261075031665641760937500 : ℚ) / 1, (-13247798979273296940926368166661389243066406250 : ℚ) / 3, (5672880036047500809675100632260364453047500000 : ℚ) / 3, (922569079142925874230948149245747974919375000 : ℚ) / 3, (-382071793874387668777451809134752881923725000 : ℚ) / 3, (81991659438646337552142507377922392686562500 : ℚ) / 1, (50675281816530814251149075444822294552705000 : ℚ) / 3, (-18336798355144515338252702074750604632525000 : ℚ) / 3, (-897709004666302286436698414797414412225000 : ℚ) / 3, (789551540950217447806951423927115703725000 : ℚ) / 3, (-7433247733022657842548225364721024712500 : ℚ) / 1, (-11129530638640304205823452811323999182500 : ℚ) / 3, (3334137007384172179580025959796713837500 : ℚ) / 3, (305143179691351520217955880239625075000 : ℚ) / 3, (-10504502138946722942710995800098287500 : ℚ) / 1, (2876504716795499420592717488602993750 : ℚ) / 3, (1090421179823999903200100655822357500 : ℚ) / 3, (53911623250111775093728106371268750 : ℚ) / 3, (0 : ℚ) / 1, (0 : ℚ) / 1]

def block05Margin0 : ℚ := (31789247722411961099287947341373912214965133088349455365316031122258370073849328912849 : ℚ) / 27487790694400000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block05_coefficient_bound_0 : ∀ i : Fin 37, block05Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block05PowerCoefficients) i := by
  decide +kernel

theorem block05_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block05PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block05Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block05PowerCoefficients
      block05Margin0 (by norm_num) block05_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block05Margin1 : ℚ := (51107261218369630292257541220662514025413224482887469703058215994256655001 : ℚ) / 64000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block05_coefficient_bound_1 : ∀ i : Fin 37, block05Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block05PowerCoefficients) i := by
  decide +kernel

theorem block05_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block05PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block05Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block05PowerCoefficients
      block05Margin1 (by norm_num) block05_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block05Margin2 : ℚ := (17179922647914939528174991084579070345924346054972005989628421488121627874728344314473 : ℚ) / 27487790694400000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block05_coefficient_bound_2 : ∀ i : Fin 37, block05Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block05PowerCoefficients) i := by
  decide +kernel

theorem block05_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block05PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block05Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block05PowerCoefficients
      block05Margin2 (by norm_num) block05_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block05Margin3 : ℚ := (103676658328437047318997689874806392235277361696052134383880274676 : ℚ) / 186264514923095703125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block05_coefficient_bound_3 : ∀ i : Fin 37, block05Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block05PowerCoefficients) i := by
  decide +kernel

theorem block05_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block05PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block05Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block05PowerCoefficients
      block05Margin3 (by norm_num) block05_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block05Margin4 : ℚ := (81787575604437385978374082826204269695726699060473801840091007558811832317 : ℚ) / 149462246265716736000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block05_coefficient_bound_4 : ∀ i : Fin 37, block05Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block05PowerCoefficients) i := by
  decide +kernel

theorem block05_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block05PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block05Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block05PowerCoefficients
      block05Margin4 (by norm_num) block05_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block05Margin5 : ℚ := (81326748302857789435637711633949464451481588913825533692609433125 : ℚ) / 147573952589676412928

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block05_coefficient_bound_5 : ∀ i : Fin 37, block05Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block05PowerCoefficients) i := by
  decide +kernel

theorem block05_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block05PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block05Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block05PowerCoefficients
      block05Margin5 (by norm_num) block05_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block05Margin6 : ℚ := (943244771073120909682275207507092900486732012114777102625838073054529048321 : ℚ) / 1600000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block05_coefficient_bound_6 : ∀ i : Fin 37, block05Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block05PowerCoefficients) i := by
  decide +kernel

theorem block05_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block05PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block05Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block05PowerCoefficients
      block05Margin6 (by norm_num) block05_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block05Margin7 : ℚ := (3675812329291308701574164926565697724095105965940182582862274134206203985471179652477 : ℚ) / 5497558138880000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block05_coefficient_bound_7 : ∀ i : Fin 37, block05Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block05PowerCoefficients) i := by
  decide +kernel

theorem block05_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block05PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block05Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block05PowerCoefficients
      block05Margin7 (by norm_num) block05_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block05Margin8 : ℚ := (148573887430901548207782786748695628269524780742053756426792434176 : ℚ) / 186264514923095703125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block05_coefficient_bound_8 : ∀ i : Fin 37, block05Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block05PowerCoefficients) i := by
  decide +kernel

theorem block05_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block05PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block05Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block05PowerCoefficients
      block05Margin8 (by norm_num) block05_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block05_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block05PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block05_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block05_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block05_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block05_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block05_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block05_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block05_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block05_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block05_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
