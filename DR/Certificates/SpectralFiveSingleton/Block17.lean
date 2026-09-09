import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (2,3). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block17PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-144557321496486328829997624063648000000000000000 : ℚ) / 7, (852179170767006695083689671926274880000000000000 : ℚ) / 7, (-1236806861080918777338413501136754802150000000000 : ℚ) / 3, (890453702385520775190349881343939251112500000000 : ℚ) / 1, (-24304789571311744419056470674491270448666640625000 : ℚ) / 21, (13153357056757562618565647189640335710208632812500 : ℚ) / 21, (14572146186435135154921050965639798128338242187500 : ℚ) / 21, (-33508615318227716051353181325855489990994882812500 : ℚ) / 21, (21511687229920491796373705473356212047680289062500 : ℚ) / 21, (9769516064693966495561883550866144347964085937500 : ℚ) / 21, (-7500278346376698878985614477036941126874581250000 : ℚ) / 7, (9422012022154562172120297519658851047772417968750 : ℚ) / 21, (1979463777277202605354787986958279510752523500000 : ℚ) / 7, (-5374867154754387823821107807368920805337557531250 : ℚ) / 21, (133686485427882900020197653064579094074803162500 : ℚ) / 21, (956095359927036527799194419757389727126635431250 : ℚ) / 21, (-277937377137908814277182039950032419280301356250 : ℚ) / 21, (-12087695601164453457924092955634709776393721875 : ℚ) / 21, (16553572372828106964522326710315890732917006875 : ℚ) / 7, (-608980133165585942332333916053109993529217500 : ℚ) / 1, (-383752216167788328611828768663457174592617250 : ℚ) / 7, (783836021631787589471418208969709329468583625 : ℚ) / 7, (-128288737718558084192679065812399899140517320 : ℚ) / 21, (-91095852602977940452429328144560556535679195 : ℚ) / 14, (4783379387887247456678903682258857588442717 : ℚ) / 7, (2063090924920723693998136174639157691598049 : ℚ) / 21, (-862700302702411856654643778487300922878450 : ℚ) / 21, (10120788164949143879364242613780227133715 : ℚ) / 6, (6261174632906442086557308368381891306830 : ℚ) / 7, (-973427564158742942182876225030638177208 : ℚ) / 7, (-76110254991673789941407114119387956742 : ℚ) / 7, (16591063184808558325151573421943538875 : ℚ) / 7, (-1711982999499491366743533174538817125 : ℚ) / 21, (-571564463423438936079584150973837915 : ℚ) / 14, (-1388763414922879326414436020123883 : ℚ) / 3, (4563079791889460643933146923264187 : ℚ) / 42]

def block17Margin0 : ℚ := (145909407536634466625827354539370399191163883015550220537204787522356553571777412988286222807 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block17_coefficient_bound_0 : ∀ i : Fin 37, block17Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block17PowerCoefficients) i := by
  decide +kernel

theorem block17_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block17PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block17Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block17PowerCoefficients
      block17Margin0 (by norm_num) block17_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block17Margin1 : ℚ := (9160630166963029613593859476110842666903650332334348653545073809389831266553198689 : ℚ) / 14000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block17_coefficient_bound_1 : ∀ i : Fin 37, block17Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block17PowerCoefficients) i := by
  decide +kernel

theorem block17_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block17PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block17Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block17PowerCoefficients
      block17Margin1 (by norm_num) block17_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block17Margin2 : ℚ := (62822300523728382029520159601300871430772468399610003091608244189132808160619257680035522807 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block17_coefficient_bound_2 : ∀ i : Fin 37, block17Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block17PowerCoefficients) i := by
  decide +kernel

theorem block17_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block17PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block17Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block17PowerCoefficients
      block17Margin2 (by norm_num) block17_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block17Margin3 : ℚ := (38421904397791199250483261041052880645852815427691732942538834052290417 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block17_coefficient_bound_3 : ∀ i : Fin 37, block17Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block17PowerCoefficients) i := by
  decide +kernel

theorem block17_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block17PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block17Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block17PowerCoefficients
      block17Margin3 (by norm_num) block17_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block17Margin4 : ℚ := (840148221584641458892727476142196967619985971504925056533538827129250597487 : ℚ) / 2318660535228167094272000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block17_coefficient_bound_4 : ∀ i : Fin 37, block17Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block17PowerCoefficients) i := by
  decide +kernel

theorem block17_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block17PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block17Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block17PowerCoefficients
      block17Margin4 (by norm_num) block17_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block17Margin5 : ℚ := (24036762173893647498902094347610426896175176361228402261164684992833 : ℚ) / 66113130760175032991744

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block17_coefficient_bound_5 : ∀ i : Fin 37, block17Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block17PowerCoefficients) i := by
  decide +kernel

theorem block17_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block17PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block17Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block17PowerCoefficients
      block17Margin5 (by norm_num) block17_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block17Margin6 : ℚ := (782781821572090497962276553259779116729465727463950030454677947517378269726462847 : ℚ) / 2000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block17_coefficient_bound_6 : ∀ i : Fin 37, block17Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block17PowerCoefficients) i := by
  decide +kernel

theorem block17_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block17PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block17Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block17PowerCoefficients
      block17Margin6 (by norm_num) block17_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block17Margin7 : ℚ := (62196726570266010146971526476055645249657716353714866015554635514312856568212966282208283527 : ℚ) / 137438953472000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block17_coefficient_bound_7 : ∀ i : Fin 37, block17Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block17PowerCoefficients) i := by
  decide +kernel

theorem block17_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block17PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block17Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block17PowerCoefficients
      block17Margin7 (by norm_num) block17_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block17Margin8 : ℚ := (8016434140206163024079429139939566667935220523137049666052434834054656 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block17_coefficient_bound_8 : ∀ i : Fin 37, block17Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block17PowerCoefficients) i := by
  decide +kernel

theorem block17_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block17PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block17Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block17PowerCoefficients
      block17Margin8 (by norm_num) block17_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block17_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block17PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block17_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block17_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block17_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block17_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block17_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block17_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block17_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block17_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block17_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
