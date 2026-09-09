import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (4,5). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block33PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-152909032231925579482499310423520000000000000000 : ℚ) / 7, (2713323356525589999664416558777838400000000000000 : ℚ) / 21, (-3071044874017773285877939453398583825100000000000 : ℚ) / 7, (6711323786328651988148397984221056657906250000000 : ℚ) / 7, (-27626312027134506347783866179674530590222500000000 : ℚ) / 21, (6813786236716000539946610487388630660404687500000 : ℚ) / 7, (442250787407849974693057657656629951762656250000 : ℚ) / 21, (-3966376236971512386692691077849399203976562500000 : ℚ) / 7, (-2282320571624773692561045894410213255717679687500 : ℚ) / 21, (8565130114890271481749758439294154871077539062500 : ℚ) / 7, (-1174549417796039873663807471999440779985048437500 : ℚ) / 1, (2059714145924301333305320795321002018970179687500 : ℚ) / 21, (4242101540568851139507411492381377158144161312500 : ℚ) / 7, (-339308068952533548422202190795415729498405156250 : ℚ) / 1, (-1186967373762084330619713588064874257884404462500 : ℚ) / 21, (253851074462300332741232701059528780884270218750 : ℚ) / 3, (-175130801854176825441118776905334136325944212500 : ℚ) / 7, (-87212668293095657130160238416806741115608687500 : ℚ) / 21, (137861110853150905222059188758330844512050998750 : ℚ) / 21, (-21950195641387919014280486151863781258547606250 : ℚ) / 21, (-7647328080921795992053539854403361635225660500 : ℚ) / 21, (5044259640362968578033025347363424677997178750 : ℚ) / 21, (-200566163882328616336220675313100107875410420 : ℚ) / 21, (-308860670739754055211653094452540813612064575 : ℚ) / 21, (17112149724429449749792080429163126083119302 : ℚ) / 7, (153783169401751042474769419768430646515570 : ℚ) / 1, (-952501293286172839773887540243343230205340 : ℚ) / 7, (251298787306192016263976568998849974093495 : ℚ) / 21, (16966051174595377023605133732816641307820 : ℚ) / 7, (-4246937814869223455350126991723691458028 : ℚ) / 7, (-6155222560821994402756225158499629260 : ℚ) / 3, (77666210398066976429618749534862077180 : ℚ) / 7, (-4787377960410881798464248090945666570 : ℚ) / 7, (-718697087451401224427561421722351965 : ℚ) / 7, (87690489913701808896454388699250898 : ℚ) / 7, (22815398959447303219665734616320935 : ℚ) / 21]

def block33Margin0 : ℚ := (13987389440628760341968066336762680897742589010786464064441471838316544279600022450617121303 : ℚ) / 13743895347200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block33_coefficient_bound_0 : ∀ i : Fin 37, block33Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block33PowerCoefficients) i := by
  decide +kernel

theorem block33_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block33PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block33Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block33PowerCoefficients
      block33Margin0 (by norm_num) block33_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block33Margin1 : ℚ := (32970938376299361524850756684506007709060054449617648335091133821389167076634529 : ℚ) / 56000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block33_coefficient_bound_1 : ∀ i : Fin 37, block33Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block33PowerCoefficients) i := by
  decide +kernel

theorem block33_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block33PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block33Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block33PowerCoefficients
      block33Margin1 (by norm_num) block33_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block33Margin2 : ℚ := (5256142701770439092286470384967691879417236991568603551795861848560363400331341975733068279 : ℚ) / 13743895347200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block33_coefficient_bound_2 : ∀ i : Fin 37, block33Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block33PowerCoefficients) i := by
  decide +kernel

theorem block33_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block33PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block33Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block33PowerCoefficients
      block33Margin2 (by norm_num) block33_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block33Margin3 : ℚ := (873115663598525406334923233992686667625015459497805051364468171012186 : ℚ) / 2910383045673370361328125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block33_coefficient_bound_3 : ∀ i : Fin 37, block33Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block33PowerCoefficients) i := by
  decide +kernel

theorem block33_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block33PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block33Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block33PowerCoefficients
      block33Margin3 (by norm_num) block33_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block33Margin4 : ℚ := (330715094054434908670820526762792787536769886768977938676772250148497648549 : ℚ) / 1159330267614083547136000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block33_coefficient_bound_4 : ∀ i : Fin 37, block33Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block33PowerCoefficients) i := by
  decide +kernel

theorem block33_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block33PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block33Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block33PowerCoefficients
      block33Margin4 (by norm_num) block33_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block33Margin5 : ℚ := (1353884506790204033162621913666873131306753802302677998334297617171 : ℚ) / 4722366482869645213696

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block33_coefficient_bound_5 : ∀ i : Fin 37, block33Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block33PowerCoefficients) i := by
  decide +kernel

theorem block33_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block33PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block33Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block33PowerCoefficients
      block33Margin5 (by norm_num) block33_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block33Margin6 : ℚ := (441495545943032915979447052052546903021820595412374747835681973515681696805943281 : ℚ) / 1400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block33_coefficient_bound_6 : ∀ i : Fin 37, block33Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block33PowerCoefficients) i := by
  decide +kernel

theorem block33_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block33PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block33Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block33PowerCoefficients
      block33Margin6 (by norm_num) block33_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block33Margin7 : ℚ := (1034319245009520218545599250253385885810386984719238445947575088553570103529597273647378331 : ℚ) / 2748779069440000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block33_coefficient_bound_7 : ∀ i : Fin 37, block33Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block33PowerCoefficients) i := by
  decide +kernel

theorem block33_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block33PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block33Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block33PowerCoefficients
      block33Margin7 (by norm_num) block33_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block33Margin8 : ℚ := (1373651535120704062442051395733253686040864876692994583063108271775744 : ℚ) / 2910383045673370361328125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block33_coefficient_bound_8 : ∀ i : Fin 37, block33Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block33PowerCoefficients) i := by
  decide +kernel

theorem block33_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block33PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block33Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block33PowerCoefficients
      block33Margin8 (by norm_num) block33_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block33_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block33PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block33_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block33_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block33_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block33_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block33_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block33_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block33_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block33_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block33_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
