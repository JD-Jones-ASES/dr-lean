import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (5,5). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block40PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-159403707969298625211289795212256000000000000000 : ℚ) / 7, (2822764415277508418373052022798046200000000000000 : ℚ) / 21, (-9525861077888615792901171193213020600500000000000 : ℚ) / 21, (61542405345099080021460088903383400460937500000000 : ℚ) / 63, (-3901467509779872463049728984538514224096875000000 : ℚ) / 3, (54505846325423186431537982878351789100171875000000 : ℚ) / 63, (14272249841282811894728772726432901660512500000000 : ℚ) / 63, (-753970135408036240587706138550453953511718750000 : ℚ) / 1, (-1060428681937638208983333811696987445553085937500 : ℚ) / 9, (91326049563799818034199941473176081790309570312500 : ℚ) / 63, (-90303090307391954249471456958836387963651804687500 : ℚ) / 63, (3718107813324757860948049995371253588704054687500 : ℚ) / 21, (42829130317445749728170076324279002307145654062500 : ℚ) / 63, (-2977630137405259057666480471571660372433398437500 : ℚ) / 7, (-2907226823249705495468075661849210300490422312500 : ℚ) / 63, (2050101370589381623378490284300009718076193437500 : ℚ) / 21, (-2201182399654380672405858021773171110697802250000 : ℚ) / 63, (-215773026368390015639815690522722139724644375000 : ℚ) / 63, (8148650898969917868316287768360846300436940625 : ℚ) / 1, (-4594210787654156300224311836549452461533265625 : ℚ) / 3, (-27389886988134959495263925874292706360516840000 : ℚ) / 63, (6207456304753601247814696129860971218621073750 : ℚ) / 21, (-984159576692018853231650447353092525836375225 : ℚ) / 63, (-1016889863574657722423151325079686544384150000 : ℚ) / 63, (10457820247332343086502614457646329628779430 : ℚ) / 3, (6706464751990549076807155644032784920668100 : ℚ) / 63, (-3537496168472702227713346660911036621187450 : ℚ) / 21, (1242524953803751913373271233758650562756725 : ℚ) / 63, (179755858748674107453938763241014740357425 : ℚ) / 63, (-7226395396724100679550890335550743992935 : ℚ) / 9, (1335191761624891586749160944064359333775 : ℚ) / 63, (1008806223916871107514199023135408095325 : ℚ) / 63, (-6878807496254421291966594513884518700 : ℚ) / 7, (-5864430308833488187898273392041318725 : ℚ) / 63, (1563350815656041298877965119796599720 : ℚ) / 63, (114076994797236516098328673081604675 : ℚ) / 63]

def block40Margin0 : ℚ := (8102929492652808898331791629154740593095997718787461169973155625381951581451485286399222303 : ℚ) / 8246337208320000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block40_coefficient_bound_0 : ∀ i : Fin 37, block40Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block40PowerCoefficients) i := by
  decide +kernel

theorem block40_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block40PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block40Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block40PowerCoefficients
      block40Margin0 (by norm_num) block40_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block40Margin1 : ℚ := (5992895857460751618076186837917961173630636004242492391606721044789146429650343 : ℚ) / 11200000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block40_coefficient_bound_1 : ∀ i : Fin 37, block40Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block40PowerCoefficients) i := by
  decide +kernel

theorem block40_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block40PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block40Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block40PowerCoefficients
      block40Margin1 (by norm_num) block40_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block40Margin2 : ℚ := (878620558647598296107924068721464492452506280008535833878849584352933404884980250036313093 : ℚ) / 2748779069440000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block40_coefficient_bound_2 : ∀ i : Fin 37, block40Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block40PowerCoefficients) i := by
  decide +kernel

theorem block40_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block40PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block40Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block40PowerCoefficients
      block40Margin2 (by norm_num) block40_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block40Margin3 : ℚ := (948477613441613928158231154862345725102375845412781156014311784050434 : ℚ) / 4074536263942718505859375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block40_coefficient_bound_3 : ∀ i : Fin 37, block40Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block40PowerCoefficients) i := by
  decide +kernel

theorem block40_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block40PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block40Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block40PowerCoefficients
      block40Margin3 (by norm_num) block40_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block40Margin4 : ℚ := (73747194563168767343574063695663745100143272191930590873904842929222117 : ℚ) / 341769168521892200448000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block40_coefficient_bound_4 : ∀ i : Fin 37, block40Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block40PowerCoefficients) i := by
  decide +kernel

theorem block40_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block40PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block40Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block40PowerCoefficients
      block40Margin4 (by norm_num) block40_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block40Margin5 : ℚ := (7159210590253312396385719008107656560861132496968401229423528055995 : ℚ) / 33056565380087516495872

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block40_coefficient_bound_5 : ∀ i : Fin 37, block40Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block40PowerCoefficients) i := by
  decide +kernel

theorem block40_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block40PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block40Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block40PowerCoefficients
      block40Margin5 (by norm_num) block40_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block40Margin6 : ℚ := (67667275914067226836621235394714171806898940832207391163701707746348758185940927 : ℚ) / 280000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block40_coefficient_bound_6 : ∀ i : Fin 37, block40Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block40PowerCoefficients) i := by
  decide +kernel

theorem block40_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block40PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block40Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block40PowerCoefficients
      block40Margin6 (by norm_num) block40_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block40Margin7 : ℚ := (489141725549422397861379311679709672966795235265946114951559098508174842148020103850769331 : ℚ) / 1649267441664000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block40_coefficient_bound_7 : ∀ i : Fin 37, block40Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block40PowerCoefficients) i := by
  decide +kernel

theorem block40_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block40PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block40Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block40PowerCoefficients
      block40Margin7 (by norm_num) block40_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block40Margin8 : ℚ := (222245330515946187253288123401071993390499937858284184058005743157248 : ℚ) / 582076609134674072265625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block40_coefficient_bound_8 : ∀ i : Fin 37, block40Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block40PowerCoefficients) i := by
  decide +kernel

theorem block40_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block40PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block40Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block40PowerCoefficients
      block40Margin8 (by norm_num) block40_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block40_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block40PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block40_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block40_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block40_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block40_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block40_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block40_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block40_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block40_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block40_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
