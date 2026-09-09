import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (2,5). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block19PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-139919680757179488024918340846048000000000000000 : ℚ) / 7, (2488724891646754345326910790620675640000000000000 : ℚ) / 21, (-8550105286632799209391429245762770643800000000000 : ℚ) / 21, (57697851779421850649602486814653924981390625000000 : ℚ) / 63, (-3988828389199244157148067471900934471118671875000 : ℚ) / 3, (73259502866785860013550512124294618923561132812500 : ℚ) / 63, (-22662420685638954763033204064431832900973652343750 : ℚ) / 63, (-1896733777501426729763146743517370591458349609375 : ℚ) / 9, (-6116775369466408896080241985086804455893849609375 : ℚ) / 63, (50474234633834742207487257115441845270365556640625 : ℚ) / 63, (-4856260165720039095616151454394384775729669140625 : ℚ) / 7, (-2453085663909278627851789008122572197993826953125 : ℚ) / 63, (28946591447091826428809708559375073712786507593750 : ℚ) / 63, (-22831018011508733584602383386232027833831430546875 : ℚ) / 126, (-4312104577925462607956300494481025818446080043750 : ℚ) / 63, (7431030335723847409999959359958593244923993328125 : ℚ) / 126, (-180714287587383449073982232051145950320915465625 : ℚ) / 21, (-192569984043673776899488157743851078104424265625 : ℚ) / 42, (255277145307926874160567067806349710846159218125 : ℚ) / 63, (-10217720078620979143065735700827546465255034375 : ℚ) / 42, (-16006839618140411509075169750991374800581449000 : ℚ) / 63, (9419287660626232022894543880176979365477214250 : ℚ) / 63, (95488079520319788048064473104777102697177430 : ℚ) / 21, (-704513418457950301845733918904851294597001725 : ℚ) / 63, (16530042017604990446371290672989311658530126 : ℚ) / 21, (252337675021640602511922736265284778795670 : ℚ) / 1, (-4507915568429826993924419624047252663626310 : ℚ) / 63, (44179142943929750081475514395530566070960 : ℚ) / 63, (39562687001923099706309978059486839460385 : ℚ) / 21, (-13438366173319335642184775487892682103767 : ℚ) / 63, (-220333979537177916942556163197433774605 : ℚ) / 9, (282267261287265411092260275376232400620 : ℚ) / 63, (-119034333725976621260407434690997045 : ℚ) / 7, (-8556624852604409022597692731508752345 : ℚ) / 126, (-66859038689858619000237848397392653 : ℚ) / 63, (22815398959447303219665734616320935 : ℚ) / 126]

def block19Margin0 : ℚ := (89673665790354056097686587375398553499891457682477200522810525113171457533583214788039653303 : ℚ) / 82463372083200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block19_coefficient_bound_0 : ∀ i : Fin 37, block19Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block19PowerCoefficients) i := by
  decide +kernel

theorem block19_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block19PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block19Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block19PowerCoefficients
      block19Margin0 (by norm_num) block19_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block19Margin1 : ℚ := (77803278763023069106173715006202978626611270010921877833121551523552767403535843 : ℚ) / 112000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block19_coefficient_bound_1 : ∀ i : Fin 37, block19Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block19PowerCoefficients) i := by
  decide +kernel

theorem block19_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block19PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block19Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block19PowerCoefficients
      block19Margin1 (by norm_num) block19_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block19Margin2 : ℚ := (13894925446869153025116917835746944862219039822706829357134995475584740138778514824163360093 : ℚ) / 27487790694400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block19_coefficient_bound_2 : ∀ i : Fin 37, block19Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block19PowerCoefficients) i := by
  decide +kernel

theorem block19_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block19PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block19Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block19PowerCoefficients
      block19Margin2 (by norm_num) block19_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block19Margin3 : ℚ := (8777715200138028328936206560001803060657275254928068464259809234367467 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block19_coefficient_bound_3 : ∀ i : Fin 37, block19Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block19PowerCoefficients) i := by
  decide +kernel

theorem block19_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block19PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block19Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block19PowerCoefficients
      block19Margin3 (by norm_num) block19_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block19Margin4 : ℚ := (1049090673002380408726669075165001335216756926369069143103522582160127197796407 : ℚ) / 2501040971504104243200000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block19_coefficient_bound_4 : ∀ i : Fin 37, block19Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block19PowerCoefficients) i := by
  decide +kernel

theorem block19_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block19PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block19Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block19PowerCoefficients
      block19Margin4 (by norm_num) block19_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block19Margin5 : ℚ := (27917182061664646664017614334508629717004554037395419299649277070199 : ℚ) / 66113130760175032991744

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block19_coefficient_bound_5 : ∀ i : Fin 37, block19Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block19PowerCoefficients) i := by
  decide +kernel

theorem block19_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block19PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block19Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block19PowerCoefficients
      block19Margin5 (by norm_num) block19_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block19Margin6 : ℚ := (1278938372884024410815160154499893795466228593067479417078594109977270830168137427 : ℚ) / 2800000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block19_coefficient_bound_6 : ∀ i : Fin 37, block19Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block19PowerCoefficients) i := by
  decide +kernel

theorem block19_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block19PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block19Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block19PowerCoefficients
      block19Margin6 (by norm_num) block19_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block19Margin7 : ℚ := (8708487342343079309942499681755715050860006866789925233175480238252892245955345025400470331 : ℚ) / 16492674416640000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block19_coefficient_bound_7 : ∀ i : Fin 37, block19Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block19PowerCoefficients) i := by
  decide +kernel

theorem block19_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block19PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block19Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block19PowerCoefficients
      block19Margin7 (by norm_num) block19_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block19Margin8 : ℚ := (1868957830953747399924585296425005436028541478866306149368505356314624 : ℚ) / 2910383045673370361328125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block19_coefficient_bound_8 : ∀ i : Fin 37, block19Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block19PowerCoefficients) i := by
  decide +kernel

theorem block19_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block19PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block19Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block19PowerCoefficients
      block19Margin8 (by norm_num) block19_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block19_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block19PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block19_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block19_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block19_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block19_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block19_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block19_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block19_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block19_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block19_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
