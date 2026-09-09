import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (3,5). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block26PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-146414356494552533753708825634784000000000000000 : ℚ) / 7, (371710978378381710759386116388387840000000000000 : ℚ) / 3, (-8887765459369138517102348602962095931400000000000 : ℚ) / 21, (19706233467998512162295841133391790570546875000000 : ℚ) / 21, (-27829374100227145316891001066025616839960859375000 : ℚ) / 21, (22527278691538151090644207012518390045183203125000 : ℚ) / 21, (-3673477597334606979206184115494936712791523437500 : ℚ) / 21, (-8071545143516561108740771605536347829819335937500 : ℚ) / 21, (-4330434703914692087363803339395542795689701171875 : ℚ) / 42, (42334381186753588120406648862216152597380380859375 : ℚ) / 42, (-38947701150802179864260646211210666221057511328125 : ℚ) / 42, (350295078499411614208343535445390916867856640625 : ℚ) / 14, (7461830019555370510284501796516564500122034359375 : ℚ) / 14, (-5410654740803854107744724579474339463329710546875 : ℚ) / 21, (-385218579622330356858332775101766588720752434375 : ℚ) / 6, (502254534144867649961629370522628734024485203125 : ℚ) / 7, (-339817388122407987085932432925967437116375303125 : ℚ) / 21, (-189333649722894613065285139462479982802572515625 : ℚ) / 42, (109660966319802829390073134908532595591799546250 : ℚ) / 21, (-25886715303820891251029790630859797021887196875 : ℚ) / 42, (-6454817553218698188499610490307508929266899000 : ℚ) / 21, (4025160386754370031311926660239952178456848250 : ℚ) / 21, (-54427495256156423970548337072260461429159585 : ℚ) / 21, (-274896287563790067825719454745480106180155750 : ℚ) / 21, (32417026460765355632903796301739202818831978 : ℚ) / 21, (4350777557780619026774841858359594978968660 : ℚ) / 21, (-2177718518913174508179239677411856442865160 : ℚ) / 21, (38991459771899087370663660526923322617295 : ℚ) / 7, (89589778838162447819491717864860173572085 : ℚ) / 42, (-811770539186597824320604226604134212729 : ℚ) / 2, (-243773301576703404549247130187644780965 : ℚ) / 14, (307274824605600394432170322258275816265 : ℚ) / 42, (-7204514826699196169375247877871359255 : ℚ) / 21, (-186478815749015245930292781358242295 : ℚ) / 2, (11705291640064268608350246455329871 : ℚ) / 3, (22815398959447303219665734616320935 : ℚ) / 42]

def block26Margin0 : ℚ := (28935279442350866613597075886595563087920382858359469528638812121264041907513943697690359303 : ℚ) / 27487790694400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block26_coefficient_bound_0 : ∀ i : Fin 37, block26Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block26PowerCoefficients) i := by
  decide +kernel

theorem block26_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block26PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block26Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block26PowerCoefficients
      block26Margin0 (by norm_num) block26_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block26Margin1 : ℚ := (10271479332508605874661595950199026165555756342160443016729934417984654886761647 : ℚ) / 16000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block26_coefficient_bound_1 : ∀ i : Fin 37, block26Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block26PowerCoefficients) i := by
  decide +kernel

theorem block26_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block26PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block26Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block26PowerCoefficients
      block26Margin1 (by norm_num) block26_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block26Margin2 : ℚ := (12215425896682565129405007412658775059781972200268682172939314793259370652467036410885006279 : ℚ) / 27487790694400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block26_coefficient_bound_2 : ∀ i : Fin 37, block26Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block26PowerCoefficients) i := by
  decide +kernel

theorem block26_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block26PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block26Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block26PowerCoefficients
      block26Margin2 (by norm_num) block26_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block26Margin3 : ℚ := (7457230675304361005066778515580086243059129282556625282572945513969151 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block26_coefficient_bound_3 : ∀ i : Fin 37, block26Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block26PowerCoefficients) i := by
  decide +kernel

theorem block26_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block26PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block26Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block26PowerCoefficients
      block26Margin3 (by norm_num) block26_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block26Margin4 : ℚ := (6998759079990346040676322050371311603455427474146804253783134035403963840277 : ℚ) / 19817772269442045050880000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block26_coefficient_bound_4 : ∀ i : Fin 37, block26Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block26PowerCoefficients) i := by
  decide +kernel

theorem block26_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block26PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block26Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block26PowerCoefficients
      block26Margin4 (by norm_num) block26_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block26Margin5 : ℚ := (23488815834446316574052537551443366408683113403673265330079209790997 : ℚ) / 66113130760175032991744

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block26_coefficient_bound_5 : ∀ i : Fin 37, block26Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block26PowerCoefficients) i := by
  decide +kernel

theorem block26_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block26PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block26Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block26PowerCoefficients
      block26Margin5 (by norm_num) block26_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block26Margin6 : ℚ := (1083832147192541762499328031739403494982571609645318345740861175062522590255514281 : ℚ) / 2800000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block26_coefficient_bound_6 : ∀ i : Fin 37, block26Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block26PowerCoefficients) i := by
  decide +kernel

theorem block26_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block26PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block26Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block26PowerCoefficients
      block26Margin6 (by norm_num) block26_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block26Margin7 : ℚ := (2492969257255415648090622283030397824831480012875569186247406205888030254877690635180116331 : ℚ) / 5497558138880000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block26_coefficient_bound_7 : ∀ i : Fin 37, block26Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block26PowerCoefficients) i := by
  decide +kernel

theorem block26_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block26PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block26Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block26PowerCoefficients
      block26Margin7 (by norm_num) block26_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block26Margin8 : ℚ := (1626364750820407626549533078788288710255239131956525956362775799631872 : ℚ) / 2910383045673370361328125

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block26_coefficient_bound_8 : ∀ i : Fin 37, block26Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block26PowerCoefficients) i := by
  decide +kernel

theorem block26_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block26PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block26Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block26PowerCoefficients
      block26Margin8 (by norm_num) block26_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block26_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block26PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block26_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block26_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block26_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block26_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block26_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block26_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block26_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block26_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block26_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
