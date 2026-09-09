import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (1,5). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block12PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-133425005019806442296127856057312000000000000000 : ℚ) / 7, (2373567485519837109698040486483720680000000000000 : ℚ) / 21, (-2733501933547009790861909204282830762500000000000 : ℚ) / 7, (18714615216015665482620905246263274812015625000000 : ℚ) / 21, (-27904591565993373772285758073624241340595703125000 : ℚ) / 21, (26107758449540788218640582515722294717113281250000 : ℚ) / 21, (-11153717781440152848303070052433007604426269531250 : ℚ) / 21, (-1052237170999950874870737474497454157456152343750 : ℚ) / 21, (-1804320777586085642864952665301460862194824218750 : ℚ) / 21, (12626687040353316473320501102477788734540488281250 : ℚ) / 21, (-9991957144331535192037901151090043891411191406250 : ℚ) / 21, (-90558871723024887711385103398108603751862500000 : ℚ) / 1, (1152495756096398234207453297162784235963937500000 : ℚ) / 3, (-2326269656039312846016490319560715835373931875000 : ℚ) / 21, (-479884352403340111547893099297728420951833593750 : ℚ) / 7, (323815987286610535103676270754216969982734531250 : ℚ) / 7, (-7423043706942557395532097545816849339728906250 : ℚ) / 3, (-31527009749961640186812617692311484169853656250 : ℚ) / 7, (20813326786687498734600872608587430809672031250 : ℚ) / 7, (1447553361966406317202118545376611983069425000 : ℚ) / 21, (-588570666873256958271147069322772875318262500 : ℚ) / 3, (2374289038768822288929316374617294128657327000 : ℚ) / 21, (235803348249626601873729440522469281884022500 : ℚ) / 21, (-186554058935761091228134275319000833709288600 : ℚ) / 21, (3641656923044201779409916474211511615098000 : ℚ) / 21, (5779235498648127731756346130853363255009500 : ℚ) / 21, (-830595900788430629930456390843212153420750 : ℚ) / 21, (-51597709091560715272422015476759381539750 : ℚ) / 21, (33098866881198827728164368898665733454150 : ℚ) / 21, (-854356639486454299654289007981831049250 : ℚ) / 21, (-473123584127709701712811192432624106500 : ℚ) / 21, (50675339122499767606075979538815667250 : ℚ) / 21, (1662187973105379951818468167080582750 : ℚ) / 7, (-625806122687297485287995858757687650 : ℚ) / 21, (-49598693390102833086229857861567250 : ℚ) / 21, (0 : ℚ) / 1]

def block12Margin0 : ℚ := (15421280205703259718465147153587338167871537585926230558589127974438832105362854811425139 : ℚ) / 13743895347200000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block12_coefficient_bound_0 : ∀ i : Fin 37, block12Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block12PowerCoefficients) i := by
  decide +kernel

theorem block12_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block12PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block12Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block12PowerCoefficients
      block12Margin0 (by norm_num) block12_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block12Margin1 : ℚ := (83649473822403478504346649635250695433439507035996226099169053451066486936727 : ℚ) / 112000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block12_coefficient_bound_1 : ∀ i : Fin 37, block12Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block12PowerCoefficients) i := by
  decide +kernel

theorem block12_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block12PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block12Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block12PowerCoefficients
      block12Margin1 (by norm_num) block12_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block12Margin2 : ℚ := (7775014290168842122363325606463006990355217710053964685679342122187394339874874570422409 : ℚ) / 13743895347200000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block12_coefficient_bound_2 : ∀ i : Fin 37, block12Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block12PowerCoefficients) i := by
  decide +kernel

theorem block12_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block12PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block12Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block12PowerCoefficients
      block12Margin2 (by norm_num) block12_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block12Margin3 : ℚ := (80577836390527939189087593657492145765701231870049069955379434648952 : ℚ) / 162981450557708740234375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block12_coefficient_bound_3 : ∀ i : Fin 37, block12Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block12PowerCoefficients) i := by
  decide +kernel

theorem block12_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block12PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block12Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block12PowerCoefficients
      block12Margin3 (by norm_num) block12_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block12Margin4 : ℚ := (82888292627749573614213888861627303006108551127592650086897543587626449302793 : ℚ) / 171202209358911897600000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block12_coefficient_bound_4 : ∀ i : Fin 37, block12Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block12PowerCoefficients) i := by
  decide +kernel

theorem block12_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block12PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block12Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block12PowerCoefficients
      block12Margin4 (by norm_num) block12_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block12Margin5 : ℚ := (2014645011112395047161620320507240759959750662793426786606593449025 : ℚ) / 4132070672510939561984

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block12_coefficient_bound_5 : ∀ i : Fin 37, block12Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block12PowerCoefficients) i := by
  decide +kernel

theorem block12_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block12PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block12Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block12PowerCoefficients
      block12Margin5 (by norm_num) block12_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block12Margin6 : ℚ := (209715104106259434149942472300203311097517438563692996543889331070364824853943 : ℚ) / 400000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block12_coefficient_bound_6 : ∀ i : Fin 37, block12Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block12PowerCoefficients) i := by
  decide +kernel

theorem block12_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block12PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block12Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block12PowerCoefficients
      block12Margin6 (by norm_num) block12_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block12Margin7 : ℚ := (1648715088184995297856870316534551656440376517304815922084785453321806833915266244231529 : ℚ) / 2748779069440000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block12_coefficient_bound_7 : ∀ i : Fin 37, block12Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block12PowerCoefficients) i := by
  decide +kernel

theorem block12_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block12PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block12Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block12PowerCoefficients
      block12Margin7 (by norm_num) block12_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block12Margin8 : ℚ := (16807117178100417983862616179135650608719136287849926920027303990272 : ℚ) / 23283064365386962890625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block12_coefficient_bound_8 : ∀ i : Fin 37, block12Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block12PowerCoefficients) i := by
  decide +kernel

theorem block12_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block12PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block12Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block12PowerCoefficients
      block12Margin8 (by norm_num) block12_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block12_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block12PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block12_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block12_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block12_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block12_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block12_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block12_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block12_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block12_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block12_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
