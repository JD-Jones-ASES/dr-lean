import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (5,0). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block35PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-170997809817565727223988003256256000000000000000 : ℚ) / 7, (1068885347015232136664839287030080400000000000000 : ℚ) / 7, (-11335775644042139673189471444674644538000000000000 : ℚ) / 21, (8356181346689933652077994445700275057578125000000 : ℚ) / 7, (-32175423462060066946362159452714376417994531250000 : ℚ) / 21, (11377552470076129775726603260889534114333984375000 : ℚ) / 21, (41620070362336910902214679786069047667628515625000 : ℚ) / 21, (-87759026332878010283058685168131856077294921875000 : ℚ) / 21, (77565632918799177905300015775126813214404453125000 : ℚ) / 21, (-14098642315838766154278627023711610309398828125000 : ℚ) / 21, (-5363970770446810470427009695992748156135437500000 : ℚ) / 3, (5073163603436918581696539660542075513429937500000 : ℚ) / 3, (-1676522925152297495768973069431658137483733750000 : ℚ) / 7, (-1340207290471483371033585527665836729337084375000 : ℚ) / 3, (1643229981709132034121026424140355606034525125000 : ℚ) / 7, (48805467285357232655917680521435793220439375000 : ℚ) / 21, (-272899274225947938867880533117100368773569000000 : ℚ) / 7, (97843426975426757822613290086220322641218437500 : ℚ) / 7, (11128304109168723427318044620910861257437862500 : ℚ) / 21, (-6008855902650486386466296463844315269545750000 : ℚ) / 3, (3329123202137491242896906544886216855916740000 : ℚ) / 7, (273775636724151912853155296355459202757052500 : ℚ) / 3, (-330744445866709781099588018328398221693884400 : ℚ) / 7, (43714200563519493469127550836473443432743000 : ℚ) / 21, (31464852263780865304127861198015076287479760 : ℚ) / 21, (-6765320339293979007985244404809260925852200 : ℚ) / 21, (308044577885151445766116202910677209300 : ℚ) / 21, (68389683685938784045342111865315803068900 : ℚ) / 7, (-8048244545984163003624835774449185013300 : ℚ) / 7, (-68980703881445336793309991578897571340 : ℚ) / 1, (731464649135444252028060558682986370900 : ℚ) / 21, (-519271138944723571261630546562911600 : ℚ) / 1, (-698538194940503189348221313783770300 : ℚ) / 3, (1031652822514138928193581043520598800 : ℚ) / 21, (91261595837789212878662938465283740 : ℚ) / 21, (0 : ℚ) / 1]

def block35Margin0 : ℚ := (1125627275617151977747008306659178887152921968900943288075780853929887888874642996214460329 : ℚ) / 1202590842880000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block35_coefficient_bound_0 : ∀ i : Fin 37, block35Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block35PowerCoefficients) i := by
  decide +kernel

theorem block35_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block35PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block35Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block35PowerCoefficients
      block35Margin0 (by norm_num) block35_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block35Margin1 : ℚ := (2426307557266824811481778565135171674559820272592132700162086694115533868770147 : ℚ) / 5000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block35_coefficient_bound_1 : ∀ i : Fin 37, block35Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block35PowerCoefficients) i := by
  decide +kernel

theorem block35_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block35PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block35Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block35PowerCoefficients
      block35Margin1 (by norm_num) block35_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block35Margin2 : ℚ := (48516236996094538141599968218677514613019143901489860996761654195167693845732041549547829 : ℚ) / 171798691840000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block35_coefficient_bound_2 : ∀ i : Fin 37, block35Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block35PowerCoefficients) i := by
  decide +kernel

theorem block35_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block35PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block35Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block35PowerCoefficients
      block35Margin2 (by norm_num) block35_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block35Margin3 : ℚ := (122734333233516841809422280271901186444348278197650003303224543869288 : ℚ) / 582076609134674072265625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block35_coefficient_bound_3 : ∀ i : Fin 37, block35Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block35PowerCoefficients) i := by
  decide +kernel

theorem block35_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block35PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block35Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block35PowerCoefficients
      block35Margin3 (by norm_num) block35_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block35Margin4 : ℚ := (76867734179097382206203639258994665888992557617660497917033704527943678642629 : ℚ) / 378635400983347200000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block35_coefficient_bound_4 : ∀ i : Fin 37, block35Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block35PowerCoefficients) i := by
  decide +kernel

theorem block35_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block35PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block35Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block35PowerCoefficients
      block35Margin4 (by norm_num) block35_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block35Margin5 : ℚ := (429191083879278445982209345885524318516802542143682053443591135245 : ℚ) / 2066035336255469780992

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block35_coefficient_bound_5 : ∀ i : Fin 37, block35Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block35PowerCoefficients) i := by
  decide +kernel

theorem block35_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block35PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block35Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block35PowerCoefficients
      block35Margin5 (by norm_num) block35_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block35Margin6 : ℚ := (8494230131355862541121170857225687193634447817883067173872168889517549272660103 : ℚ) / 35000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block35_coefficient_bound_6 : ∀ i : Fin 37, block35Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block35PowerCoefficients) i := by
  decide +kernel

theorem block35_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block35PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block35Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block35PowerCoefficients
      block35Margin6 (by norm_num) block35_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block35Margin7 : ℚ := (52378841969014212042540447049453628448057319408507882977938888036920520256563226967488121 : ℚ) / 171798691840000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block35_coefficient_bound_7 : ∀ i : Fin 37, block35Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block35PowerCoefficients) i := by
  decide +kernel

theorem block35_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block35PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block35Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block35PowerCoefficients
      block35Margin7 (by norm_num) block35_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block35Margin8 : ℚ := (1613667451278427594925942681193746958772642430040226849035070314943488 : ℚ) / 4074536263942718505859375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block35_coefficient_bound_8 : ∀ i : Fin 37, block35Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block35PowerCoefficients) i := by
  decide +kernel

theorem block35_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block35PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block35Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block35PowerCoefficients
      block35Margin8 (by norm_num) block35_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block35_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block35PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block35_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block35_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block35_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block35_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block35_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block35_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block35_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block35_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block35_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
