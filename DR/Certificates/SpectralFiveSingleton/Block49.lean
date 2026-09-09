import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (7,0). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block49PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-26283880184615974097366996119104000000000000000 : ℚ) / 1, (168344016622493078034328179934142840000000000000 : ℚ) / 1, (-607399762344950268377416736438322243800000000000 : ℚ) / 1, (1372594102291459101018076570288644754078125000000 : ℚ) / 1, (-1829607454037681469715984032005458019051406250000 : ℚ) / 1, (793630524543220699873477117967963010557421875000 : ℚ) / 1, (2082567085684128269603856306615592048460117187500 : ℚ) / 1, (-4782595304693805905634356858713241723333300781250 : ℚ) / 1, (4483736706155063343167467060858816929956363281250 : ℚ) / 1, (-1083226522457196678487524027614836912748808593750 : ℚ) / 1, (-1973695850249818445417411052081451557827239843750 : ℚ) / 1, (2100214054511961729921880844675700403107408593750 : ℚ) / 1, (-440523622394193392606473671153209361773517000000 : ℚ) / 1, (-504707179371516195962113136592331991127004843750 : ℚ) / 1, (323862724238300617683426485996504096331747537500 : ℚ) / 1, (-22390993817619192142414579802326633590982312500 : ℚ) / 1, (-51349788766782358424332577147983605934935856250 : ℚ) / 1, (22574870859450677613030569388192399101529500000 : ℚ) / 1, (594144667877546055736232434291694546137161250 : ℚ) / 1, (-2898977226610395263697021713260766950851350000 : ℚ) / 1, (644173679172882521664974128605310070993142000 : ℚ) / 1, (107436419818181108814052201843351326571523500 : ℚ) / 1, (-65824588725073869014799347387125452364631320 : ℚ) / 1, (5083395480818271891024167231098699970314600 : ℚ) / 1, (2260741912007471216536322068168011427303376 : ℚ) / 1, (-478631187822301408303107491227339385174920 : ℚ) / 1, (14110655838680780031113087650132931482280 : ℚ) / 1, (16491423428201526429873208453027918894870 : ℚ) / 1, (-1558133243559345774305162634179860522790 : ℚ) / 1, (215229000849248161971691317642509886 : ℚ) / 1, (70196473092654128846963389234064452490 : ℚ) / 1, (426949504010964686102423959872437940 : ℚ) / 1, (-77982508197926073994278730466412110 : ℚ) / 1, (123004759607455026053850047496686780 : ℚ) / 1, (9126159583778921287866293846528374 : ℚ) / 1, (0 : ℚ) / 1]

def block49Margin0 : ℚ := (1503092220433700828700254740686801338480498949389357055505432346914693804325194961896269987 : ℚ) / 1717986918400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block49_coefficient_bound_0 : ∀ i : Fin 37, block49Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block49PowerCoefficients) i := by
  decide +kernel

theorem block49_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block49PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block49Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block49PowerCoefficients
      block49Margin0 (by norm_num) block49_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block49Margin1 : ℚ := (20186354542775887619347773507544906292842768495215329652743023231016992016812587 : ℚ) / 50000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block49_coefficient_bound_1 : ∀ i : Fin 37, block49Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block49PowerCoefficients) i := by
  decide +kernel

theorem block49_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block49PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block49Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block49PowerCoefficients
      block49Margin1 (by norm_num) block49_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block49Margin2 : ℚ := (341560208841014597409736074989827046158596945890579911041979153242523895805607402197425409 : ℚ) / 1717986918400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block49_coefficient_bound_2 : ∀ i : Fin 37, block49Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block49PowerCoefficients) i := by
  decide +kernel

theorem block49_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block49PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block49Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block49PowerCoefficients
      block49Margin2 (by norm_num) block49_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block49Margin3 : ℚ := (384094675065473190778861991729930877213695610576067661444818507789524 : ℚ) / 2910383045673370361328125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block49_coefficient_bound_3 : ∀ i : Fin 37, block49Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block49PowerCoefficients) i := by
  decide +kernel

theorem block49_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block49PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block49Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block49PowerCoefficients
      block49Margin3 (by norm_num) block49_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block49Margin4 : ℚ := (36194671565969444581659586466715776963005669828561351339721795966142030135901 : ℚ) / 285076611072000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block49_coefficient_bound_4 : ∀ i : Fin 37, block49Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block49PowerCoefficients) i := by
  decide +kernel

theorem block49_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block49PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block49Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block49PowerCoefficients
      block49Margin4 (by norm_num) block49_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block49Margin5 : ℚ := (79477726165218878096322203898732527330073798231537307468195854147 : ℚ) / 590295810358705651712

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block49_coefficient_bound_5 : ∀ i : Fin 37, block49Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block49PowerCoefficients) i := by
  decide +kernel

theorem block49_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block49PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block49Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block49PowerCoefficients
      block49Margin5 (by norm_num) block49_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block49Margin6 : ℚ := (8691894049256902523318658216311239030865958157491994405679792265813372498325809 : ℚ) / 50000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block49_coefficient_bound_6 : ∀ i : Fin 37, block49Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block49PowerCoefficients) i := by
  decide +kernel

theorem block49_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block49PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block49Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block49PowerCoefficients
      block49Margin6 (by norm_num) block49_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block49Margin7 : ℚ := (407878216951269175480768532413051155142280187671307748230183775796563415986213579010771541 : ℚ) / 1717986918400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block49_coefficient_bound_7 : ∀ i : Fin 37, block49Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block49PowerCoefficients) i := by
  decide +kernel

theorem block49_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block49PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block49Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block49PowerCoefficients
      block49Margin7 (by norm_num) block49_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block49Margin8 : ℚ := (948863829055137261834467633299290454218686381032388885999069605343232 : ℚ) / 2910383045673370361328125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block49_coefficient_bound_8 : ∀ i : Fin 37, block49Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block49PowerCoefficients) i := by
  decide +kernel

theorem block49_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block49PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block49Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block49PowerCoefficients
      block49Margin8 (by norm_num) block49_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block49_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block49PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block49_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block49_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block49_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block49_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block49_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block49_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block49_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block49_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block49_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
