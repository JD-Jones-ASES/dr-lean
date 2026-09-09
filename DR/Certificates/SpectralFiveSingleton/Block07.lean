import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (1,0). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block07PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-145019106868073544308826064101312000000000000000 : ℚ) / 7, (842218011830794894953610221856578560000000000000 : ℚ) / 7, (-401509511975069629130820353046364800000000000000 : ℚ) / 1, (5874622776892348225260265871314917632000000000000 : ℚ) / 7, (-6933991211791949038594591048173895840000000000000 : ℚ) / 7, (1525934211803847138499711804668485792000000000000 : ℚ) / 7, (1426177610846419891839185200287609280000000000000 : ℚ) / 1, (-17818039842641895266203565717857624620800000000000 : ℚ) / 7, (12789757571520911490038708305961067992000000000000 : ℚ) / 7, (155611193994633355277418899260451234240000000000 : ℚ) / 1, (-8868885311861028831611413943861718777680000000000 : ℚ) / 7, (5450004645799681744003395733216579394710400000000 : ℚ) / 7, (870564040906949084365231133114607559336000000000 : ℚ) / 7, (-2016576816402884788621833613439789514405920000000 : ℚ) / 7, (429466677195944696520498031811490278178400000000 : ℚ) / 7, (28360183659436473224058330164754843257120000000 : ℚ) / 1, (-122065527712988958999403598743512317951000000000 : ℚ) / 7, (17140133599216764113496642630111595957744000000 : ℚ) / 7, (1126871464631351135062513062987250322540000000 : ℚ) / 1, (-5596150806747547248354087265583885279640400000 : ℚ) / 7, (639361763906966916889509699338104487011200000 : ℚ) / 7, (73527380192232056636048837043418022739712000 : ℚ) / 1, (-88712651393495498699499137763172748025840000 : ℚ) / 7, (-13432525464894873587595213704624845753371200 : ℚ) / 7, (649676792071267527494993457612319128122000 : ℚ) / 1, (-142374697210928358805886976109946788061000 : ℚ) / 7, (-88711932489699271472662313742708201219000 : ℚ) / 7, (19124014755828138188670561011216460203000 : ℚ) / 7, (802366915641753062560753170824840441800 : ℚ) / 7, (-346069469122295882032408513673160638000 : ℚ) / 7, (20393969185053238517309966897213897000 : ℚ) / 7, (567417826135772391946768412882151000 : ℚ) / 1, (-405415406840840548704835359911941000 : ℚ) / 7, (-39678954712082266468983886289253800 : ℚ) / 7, (0 : ℚ) / 1, (0 : ℚ) / 1]

def block07Margin0 : ℚ := (6348751945745574526737961464997955288191852346867915246715559859432008016272587401753631 : ℚ) / 6012954214400000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block07_coefficient_bound_0 : ∀ i : Fin 37, block07Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block07PowerCoefficients) i := by
  decide +kernel

theorem block07_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block07PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block07Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block07PowerCoefficients
      block07Margin0 (by norm_num) block07_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block07Margin1 : ℚ := (32023248300569127570570750814587569153707279688355565573082831679989354852883 : ℚ) / 50000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block07_coefficient_bound_1 : ∀ i : Fin 37, block07Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block07PowerCoefficients) i := by
  decide +kernel

theorem block07_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block07PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block07Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block07PowerCoefficients
      block07Margin1 (by norm_num) block07_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block07Margin2 : ℚ := (373329428078441537007656471119665132366966343958276111276100262791704142235691702848377 : ℚ) / 858993459200000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block07_coefficient_bound_2 : ∀ i : Fin 37, block07Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block07PowerCoefficients) i := by
  decide +kernel

theorem block07_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block07PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block07Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block07PowerCoefficients
      block07Margin2 (by norm_num) block07_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block07Margin3 : ℚ := (8050247379422697941434429943404307525497248525441130444255543997664 : ℚ) / 23283064365386962890625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block07_coefficient_bound_3 : ∀ i : Fin 37, block07Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block07PowerCoefficients) i := by
  decide +kernel

theorem block07_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block07PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block07Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block07PowerCoefficients
      block07Margin3 (by norm_num) block07_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block07Margin4 : ℚ := (83236135621423690148117172721320945636371347909778269348193402775 : ℚ) / 258254417031933722624

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block07_coefficient_bound_4 : ∀ i : Fin 37, block07Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block07PowerCoefficients) i := by
  decide +kernel

theorem block07_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block07PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block07Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block07PowerCoefficients
      block07Margin4 (by norm_num) block07_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block07Margin5 : ℚ := (166458526193767918037992273536245711954042696931263100428336756715 : ℚ) / 516508834063867445248

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block07_coefficient_bound_5 : ∀ i : Fin 37, block07Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block07PowerCoefficients) i := by
  decide +kernel

theorem block07_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block07PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block07Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block07PowerCoefficients
      block07Margin5 (by norm_num) block07_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block07Margin6 : ℚ := (118430748768179955328436489482885291348203250579963794739338612096160939775289 : ℚ) / 350000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block07_coefficient_bound_6 : ∀ i : Fin 37, block07Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block07PowerCoefficients) i := by
  decide +kernel

theorem block07_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block07PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block07Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block07PowerCoefficients
      block07Margin6 (by norm_num) block07_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block07Margin7 : ℚ := (330030023780085894005312679759164163319546250227582707705201535940861245750567785990417 : ℚ) / 858993459200000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block07_coefficient_bound_7 : ∀ i : Fin 37, block07Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block07PowerCoefficients) i := by
  decide +kernel

theorem block07_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block07PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block07Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block07PowerCoefficients
      block07Margin7 (by norm_num) block07_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block07Margin8 : ℚ := (75140136110503029798255090590956600913576950560902383621659407941632 : ℚ) / 162981450557708740234375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block07_coefficient_bound_8 : ∀ i : Fin 37, block07Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block07PowerCoefficients) i := by
  decide +kernel

theorem block07_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block07PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block07Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block07PowerCoefficients
      block07Margin8 (by norm_num) block07_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block07_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block07PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block07_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block07_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block07_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block07_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block07_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block07_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block07_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block07_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block07_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
