import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (0,0). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block00PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-19789204447242928368576511330368000000000000000 : ℚ) / 1, (111994757680550368546533960313920000000000000000 : ℚ) / 1, (-366391647660263178502549601583449600000000000000 : ℚ) / 1, (751421600795100086728232957540992000000000000000 : ℚ) / 1, (-864560388711372628850374008562297600000000000000 : ℚ) / 1, (163203739564042378589134603869616000000000000000 : ℚ) / 1, (1247759364773844251116069776799570240000000000000 : ℚ) / 1, (-2113216722081752440205467207910416000000000000000 : ℚ) / 1, (1379574809084449885511032663527500896000000000000 : ℚ) / 1, (308139336016712644776374363373418752000000000000 : ℚ) / 1, (-1100070229274374396349989353507331125120000000000 : ℚ) / 1, (557733701192115170596862222558616968800000000000 : ℚ) / 1, (184176115007423598628874526978361031376000000000 : ℚ) / 1, (-237286157307951833072100296503587224720000000000 : ℚ) / 1, (23985032493808418109345151553257604848000000000 : ℚ) / 1, (27522381674774673287265664235127720080000000000 : ℚ) / 1, (-13570044976347320882495593302934905643200000000 : ℚ) / 1, (57789919345260238261350426920461068000000000 : ℚ) / 1, (1058999507513549539574335398147524271120000000 : ℚ) / 1, (-548524725932254682677806593177074623280000000 : ℚ) / 1, (17827969650943783644648067525569809084800000 : ℚ) / 1, (64800519985266085321097515933539310008000000 : ℚ) / 1, (-4300882987856301922117063635358591032640000 : ℚ) / 1, (-1889943527575063997013332949259344046200000 : ℚ) / 1, (475702368586957506589175945828255418300000 : ℚ) / 1, (38580546694553687303376495582051195700000 : ℚ) / 1, (-8461304065270692638389341542294134900000 : ℚ) / 1, (1652411588289203603740942104832605960000 : ℚ) / 1, (327747868853977260096260774424321400000 : ℚ) / 1, (-9161801239263876902667750832982850000 : ℚ) / 1, (1532458269111402670688564166087275000 : ℚ) / 1, (768826627218985314380122560425050000 : ℚ) / 1, (43129298600089420074982485097015000 : ℚ) / 1, (0 : ℚ) / 1, (0 : ℚ) / 1, (0 : ℚ) / 1]

def block00Margin0 : ℚ := (1864548934822604774811171389522961325948314424685277462009983070720762239001832341603 : ℚ) / 1717986918400000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block00_coefficient_bound_0 : ∀ i : Fin 37, block00Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block00PowerCoefficients) i := by
  decide +kernel

theorem block00_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block00PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block00Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block00PowerCoefficients
      block00Margin0 (by norm_num) block00_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block00Margin1 : ℚ := (135510647764755941444501891523295560172846608047891187266983639269525045003 : ℚ) / 200000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block00_coefficient_bound_1 : ∀ i : Fin 37, block00Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block00PowerCoefficients) i := by
  decide +kernel

theorem block00_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block00PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block00Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block00PowerCoefficients
      block00Margin1 (by norm_num) block00_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block00Margin2 : ℚ := (806320667001440066762589805288232829043970540542754966397749058273241744686271194969 : ℚ) / 1717986918400000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block00_coefficient_bound_2 : ∀ i : Fin 37, block00Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block00PowerCoefficients) i := by
  decide +kernel

theorem block00_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block00PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block00Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block00PowerCoefficients
      block00Margin2 (by norm_num) block00_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block00Margin3 : ℚ := (69720430721751012512311582607409813805619675140144268718010176624 : ℚ) / 186264514923095703125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block00_coefficient_bound_3 : ∀ i : Fin 37, block00Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block00PowerCoefficients) i := by
  decide +kernel

theorem block00_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block00PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block00Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block00PowerCoefficients
      block00Margin3 (by norm_num) block00_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block00Margin4 : ℚ := (3169927008661130466013597927134820003605200784017523737369401875 : ℚ) / 9223372036854775808

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block00_coefficient_bound_4 : ∀ i : Fin 37, block00Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block00PowerCoefficients) i := by
  decide +kernel

theorem block00_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block00PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block00Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block00PowerCoefficients
      block00Margin4 (by norm_num) block00_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block00Margin5 : ℚ := (51891116551549669629600379254865545895827810782472313910810644168096583 : ℚ) / 151422728831227238809600000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block00_coefficient_bound_5 : ∀ i : Fin 37, block00Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block00PowerCoefficients) i := by
  decide +kernel

theorem block00_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block00PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block00Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block00PowerCoefficients
      block00Margin5 (by norm_num) block00_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block00Margin6 : ℚ := (70506143311438333650678158034745028003502005540966739744552042317077005369 : ℚ) / 200000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block00_coefficient_bound_6 : ∀ i : Fin 37, block00Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block00PowerCoefficients) i := by
  decide +kernel

theorem block00_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block00PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block00Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block00PowerCoefficients
      block00Margin6 (by norm_num) block00_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block00Margin7 : ℚ := (671725833826728568564569350702086627897138434309134117760837222906892235502135505221 : ℚ) / 1717986918400000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block00_coefficient_bound_7 : ∀ i : Fin 37, block00Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block00PowerCoefficients) i := by
  decide +kernel

theorem block00_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block00PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block00Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block00PowerCoefficients
      block00Margin7 (by norm_num) block00_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block00Margin8 : ℚ := (85600565059933751498052778618392614259978740950564889948489515008 : ℚ) / 186264514923095703125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block00_coefficient_bound_8 : ∀ i : Fin 37, block00Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block00PowerCoefficients) i := by
  decide +kernel

theorem block00_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block00PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block00Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block00PowerCoefficients
      block00Margin8 (by norm_num) block00_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block00_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block00PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block00_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block00_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block00_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block00_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block00_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block00_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block00_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block00_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block00_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
