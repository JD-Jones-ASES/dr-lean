import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (2,4). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block18PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-142238501126832908427457982454848000000000000000 : ℚ) / 7, (2519880784154834326657852334466937640000000000000 : ℚ) / 21, (-2860193181593329732064207679659578704600000000000 : ℚ) / 7, (56580150936461374127868185973417978651715625000000 : ℚ) / 63, (-77408480205829612031108440735044873853681562500000 : ℚ) / 63, (54449251712448568043845243439130646693743906250000 : ℚ) / 63, (4427901846340727822813916241568095684386484375000 : ℚ) / 21, (-59584733963650611852020910315618538960121328125000 : ℚ) / 63, (1457107827916944935100638246015448108394421875000 : ℚ) / 3, (5736091873795101766280746506781243994270281250000 : ℚ) / 9, (-2698091071382465688896317627677014959361293750000 : ℚ) / 3, (13591688977202900774257566481266620523587860937500 : ℚ) / 63, (23349025388114160252173125665321972418365498218750 : ℚ) / 63, (-1550352286207388005634211362122595857245757062500 : ℚ) / 7, (-270261769704710240543770300073031197292413131250 : ℚ) / 9, (1100828291604249389157687211829715630230295512500 : ℚ) / 21, (-680546706825666499847215256587513447754222693750 : ℚ) / 63, (-159585634233314483157088286799639909845904387500 : ℚ) / 63, (21944150423331662087273275233624971403481585000 : ℚ) / 7, (-9225367832139784046587646932984079545915171250 : ℚ) / 21, (-1062620990243259577043291832601234163508186000 : ℚ) / 7, (8155104728070768086277965938443734188347897500 : ℚ) / 63, (-5708301436761448863084501996175752855645190 : ℚ) / 7, (-549753786111292835957705414511266701907134520 : ℚ) / 63, (45088336858330571979967952066223213041440228 : ℚ) / 63, (3624211780585860522673531325079879411378872 : ℚ) / 21, (-3470727616383341112035181200427330183732080 : ℚ) / 63, (71304362330914168225619014482846361388890 : ℚ) / 63, (28573543770198557481637683824054734813250 : ℚ) / 21, (-10881480255039035359249862172042391653382 : ℚ) / 63, (-366896175392291995914566544900886535798 : ℚ) / 21, (211432851604056535612861112324304841810 : ℚ) / 63, (-1083233897343969636095781426724081630 : ℚ) / 21, (-3410940358000607351500077122433347770 : ℚ) / 63, (-48011535201619542427470502409997098 : ℚ) / 63, (9126159583778921287866293846528374 : ℚ) / 63]

def block18Margin0 : ℚ := (110739790139998576325795061931843817626295602452540399020164954772865479533832538425069741867 : ℚ) / 103079215104000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block18_coefficient_bound_0 : ∀ i : Fin 37, block18Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block18PowerCoefficients) i := by
  decide +kernel

theorem block18_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block18PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block18Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block18PowerCoefficients
      block18Margin0 (by norm_num) block18_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block18Margin1 : ℚ := (2358711994610586414079404422213160856144988100881424692617141025605554136386866133 : ℚ) / 3500000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block18_coefficient_bound_1 : ∀ i : Fin 37, block18Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block18PowerCoefficients) i := by
  decide +kernel

theorem block18_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block18PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block18Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block18PowerCoefficients
      block18Margin1 (by norm_num) block18_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block18Margin2 : ℚ := (16505620378137476504111819311064660210196991417537254125915979346234594002050568072619415409 : ℚ) / 34359738368000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block18_coefficient_bound_2 : ∀ i : Fin 37, block18Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block18PowerCoefficients) i := by
  decide +kernel

theorem block18_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block18PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block18Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block18PowerCoefficients
      block18Margin2 (by norm_num) block18_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block18Margin3 : ℚ := (41034111243662179778953835123268768483022636158382514654343478814626376 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block18_coefficient_bound_3 : ∀ i : Fin 37, block18Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block18PowerCoefficients) i := by
  decide +kernel

theorem block18_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block18PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block18Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block18PowerCoefficients
      block18Margin3 (by norm_num) block18_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block18Margin4 : ℚ := (7622212629904043517138319657451215650373298158117449778220295148820761797167 : ℚ) / 19563698265987659857920000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block18_coefficient_bound_4 : ∀ i : Fin 37, block18Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block18PowerCoefficients) i := by
  decide +kernel

theorem block18_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block18PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block18Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block18PowerCoefficients
      block18Margin4 (by norm_num) block18_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block18Margin5 : ℚ := (6470549068089269827154801167350790844515503148022209951566232662879 : ℚ) / 16528282690043758247936

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block18_coefficient_bound_5 : ∀ i : Fin 37, block18Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block18PowerCoefficients) i := by
  decide +kernel

theorem block18_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block18PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block18Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block18PowerCoefficients
      block18Margin5 (by norm_num) block18_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block18Margin6 : ℚ := (1478318861767350948548250292981298789426234475020780575412236186094092665619209633 : ℚ) / 3500000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block18_coefficient_bound_6 : ∀ i : Fin 37, block18Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block18PowerCoefficients) i := by
  decide +kernel

theorem block18_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block18PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block18Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block18PowerCoefficients
      block18Margin6 (by norm_num) block18_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block18Margin7 : ℚ := (50326485336107109216968934547061080216767792507219759590433641666695312976568360434408201107 : ℚ) / 103079215104000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block18_coefficient_bound_7 : ∀ i : Fin 37, block18Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block18PowerCoefficients) i := by
  decide +kernel

theorem block18_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block18PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block18Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block18PowerCoefficients
      block18Margin7 (by norm_num) block18_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block18Margin8 : ℚ := (8643383990941057289644097900284945445660814822998837816140025979813888 : ℚ) / 14551915228366851806640625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block18_coefficient_bound_8 : ∀ i : Fin 37, block18Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block18PowerCoefficients) i := by
  decide +kernel

theorem block18_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block18PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block18Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block18PowerCoefficients
      block18Margin8 (by norm_num) block18_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block18_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block18PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block18_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block18_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block18_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block18_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block18_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block18_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block18_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block18_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block18_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
