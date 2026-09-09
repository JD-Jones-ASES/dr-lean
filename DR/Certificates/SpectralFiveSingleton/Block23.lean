import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (3,2). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block23PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-153370817603512794961327750461184000000000000000 : ℚ) / 7, (2746567794456575313564154207535302880000000000000 : ℚ) / 21, (-9343892560561724858973466516664507151400000000000 : ℚ) / 21, (19984807452485476732823735895546548609256250000000 : ℚ) / 21, (-24791237548528875285860547427876284992525312500000 : ℚ) / 21, (2968408073299097761942668243689540794612656250000 : ℚ) / 7, (27573358641987055444949366132903339830827031250000 : ℚ) / 21, (-53630767374992118100302544975209272986938593750000 : ℚ) / 21, (12990145380101759294498761516711660188486343750000 : ℚ) / 7, (1598170514776778066320945682170401850029156250000 : ℚ) / 7, (-29382620312911044025354259485141184474441075000000 : ℚ) / 21, (17711005475848219881792098679940983321291218750000 : ℚ) / 21, (1157714705631829865684466592407518746529820500000 : ℚ) / 7, (-2390886950324971851567449017851825479205827000000 : ℚ) / 7, (495138022727515347051261005686431958692592850000 : ℚ) / 7, (842218357489867284892238100690272539817938550000 : ℚ) / 21, (-459186011796894845072489671983462408423483725000 : ℚ) / 21, (61761443374753203446165466067450872845223837500 : ℚ) / 21, (14398551195483369847779294947753252716294317500 : ℚ) / 7, (-1050537591492993737687715876267505399727160000 : ℚ) / 1, (489228740525456394816710203565566462529892000 : ℚ) / 7, (2347767800816628846610142963793834940791510500 : ℚ) / 21, (-389860381649101110349761167120116067846506960 : ℚ) / 21, (-97516752093668706742831364696683847491587260 : ℚ) / 21, (21268466231404414660026067135220343776871128 : ℚ) / 21, (-587473891189734158261361700860931984826272 : ℚ) / 21, (-115146660756742493526902602291891536029860 : ℚ) / 3, (31839104501631102443575392323494803690900 : ℚ) / 7, (2547228455033178968146730286629757677230 : ℚ) / 7, (-538661431036679204376524105427752766766 : ℚ) / 3, (949748999239019035003329148544082878 : ℚ) / 1, (6608186899475305918689608036784544070 : ℚ) / 3, (-5242248560482582229187666011138723260 : ℚ) / 21, (-206410436232182027776059728680680455 : ℚ) / 7, (49201903842982010421540018998674712 : ℚ) / 21, (4563079791889460643933146923264187 : ℚ) / 21]

def block23Margin0 : ℚ := (489496591064371100299388694525102605864230871910056032593679357867060056145630948037028710809 : ℚ) / 481036337152000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block23_coefficient_bound_0 : ∀ i : Fin 37, block23Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block23PowerCoefficients) i := by
  decide +kernel

theorem block23_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block23PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block23Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block23PowerCoefficients
      block23Margin0 (by norm_num) block23_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block23Margin1 : ℚ := (4143828621569402822756105021762346190647399822750153860276109351656423455216438269 : ℚ) / 7000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block23_coefficient_bound_1 : ∀ i : Fin 37, block23Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block23PowerCoefficients) i := by
  decide +kernel

theorem block23_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block23PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block23Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block23PowerCoefficients
      block23Margin1 (by norm_num) block23_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block23Margin2 : ℚ := (26753185017351435753177317769666826803494291917750758817604019751583702949915487236011573967 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block23_coefficient_bound_2 : ∀ i : Fin 37, block23Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block23PowerCoefficients) i := by
  decide +kernel

theorem block23_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block23PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block23Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block23PowerCoefficients
      block23Margin2 (by norm_num) block23_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block23Margin3 : ℚ := (31511122336554793824041871198721438433076542143109862002096518813165374 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block23_coefficient_bound_3 : ∀ i : Fin 37, block23Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block23PowerCoefficients) i := by
  decide +kernel

theorem block23_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block23PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block23Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block23PowerCoefficients
      block23Margin3 (by norm_num) block23_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block23Margin4 : ℚ := (40290728611406603065269728684486218463052150309463939577313962631969490081 : ℚ) / 136391796189892182016000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block23_coefficient_bound_4 : ∀ i : Fin 37, block23Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block23PowerCoefficients) i := by
  decide +kernel

theorem block23_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block23PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block23Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block23PowerCoefficients
      block23Margin4 (by norm_num) block23_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block23Margin5 : ℚ := (9814283715299391619909794642241640306460553275658122101402531811225 : ℚ) / 33056565380087516495872

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block23_coefficient_bound_5 : ∀ i : Fin 37, block23Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block23PowerCoefficients) i := by
  decide +kernel

theorem block23_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block23PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block23Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block23PowerCoefficients
      block23Margin5 (by norm_num) block23_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block23Margin6 : ℚ := (2274054041374426440555861392020357181744277740484745712876476689065945526855574989 : ℚ) / 7000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block23_coefficient_bound_6 : ∀ i : Fin 37, block23Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block23PowerCoefficients) i := by
  decide +kernel

theorem block23_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block23PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block23Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block23PowerCoefficients
      block23Margin6 (by norm_num) block23_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block23Margin7 : ℚ := (26371216914056163389317045033923038618702909266032079563528296782550925475967517504740770367 : ℚ) / 68719476736000000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block23_coefficient_bound_7 : ∀ i : Fin 37, block23Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block23PowerCoefficients) i := by
  decide +kernel

theorem block23_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block23PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block23Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block23PowerCoefficients
      block23Margin7 (by norm_num) block23_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block23Margin8 : ℚ := (48499451059272692203862741628770204371091031280747131876693902612219904 : ℚ) / 101863406598567962646484375

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block23_coefficient_bound_8 : ∀ i : Fin 37, block23Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block23PowerCoefficients) i := by
  decide +kernel

theorem block23_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block23PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block23Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block23PowerCoefficients
      block23Margin8 (by norm_num) block23_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block23_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block23PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block23_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block23_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block23_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block23_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block23_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block23_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block23_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block23_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block23_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
