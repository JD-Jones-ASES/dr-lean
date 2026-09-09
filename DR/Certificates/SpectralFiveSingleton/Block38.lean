import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (5,3). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block38PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-164041348708605466016369078429856000000000000000 : ℚ) / 7, (986606186223488761078270981906016400000000000000 : ℚ) / 7, (-10083438357185235238655578765824580331750000000000 : ℚ) / 21, (7165372122358882731478427580310378191781250000000 : ℚ) / 7, (-26553574003441067951495484449455663814019921875000 : ℚ) / 21, (3133040386264329912924732608389204502830859375000 : ℚ) / 7, (29191083705945912929570273363744176785262304687500 : ℚ) / 21, (-55483944281094639436961056387571978512255468750000 : ℚ) / 21, (24859121469351393666955388538311834172780458984375 : ℚ) / 14, (21400718687142638154460566675413382501655302734375 : ℚ) / 42, (-70863248856590765769415062932929957387212970703125 : ℚ) / 42, (38419384292350507309075986539510055875830982421875 : ℚ) / 42, (11225805667224084378430529973677128734639732265625 : ℚ) / 42, (-9372199105568035981077956295692353654983181953125 : ℚ) / 21, (3398604886331168874464339283079004371235783171875 : ℚ) / 42, (1208517022644584755025934552796450891974292203125 : ℚ) / 21, (-735501360448840454412213796706476143981954578125 : ℚ) / 21, (157350927942408373430865806760900176498509859375 : ℚ) / 42, (31131181675422642676589975493137171899572959375 : ℚ) / 7, (-69033568827606130786222250740552964780661803125 : ℚ) / 42, (-1097263871801158468807412267856285483080623750 : ℚ) / 21, (3944738150471526836891936705692319054969735000 : ℚ) / 21, (-535194186681108065664945421023389253495951950 : ℚ) / 21, (-160768681980263526540294818644926303095920300 : ℚ) / 21, (15874080241786216968936378303968305927661420 : ℚ) / 7, (-372400981844425845114535779906680772458670 : ℚ) / 7, (-1785502847595397384310739184638331931510000 : ℚ) / 21, (275520496203494963924072680750709985512150 : ℚ) / 21, (22989456256501387191341772656908715924275 : ℚ) / 21, (-1275627173651210179813861970493930502945 : ℚ) / 3, (167304745187460884412050953427397677955 : ℚ) / 7, (59023557147732749144758312408631872625 : ℚ) / 7, (-1669806504889852811651217098787566500 : ℚ) / 3, (-158502325232130619911338086100170575 : ℚ) / 7, (349174801466323944927058199345433440 : ℚ) / 21, (22815398959447303219665734616320935 : ℚ) / 21]

def block38Margin0 : ℚ := (92626279783179827706535925055921478874257317557685946294420944492500162627158771313164286649 : ℚ) / 96207267430400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block38_coefficient_bound_0 : ∀ i : Fin 37, block38Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block38PowerCoefficients) i := by
  decide +kernel

theorem block38_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block38PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block38Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block38PowerCoefficients
      block38Margin0 (by norm_num) block38_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block38Margin1 : ℚ := (717162126220916644912571522150868839993776376932143462520616910298410765450282189 : ℚ) / 1400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block38_coefficient_bound_1 : ∀ i : Fin 37, block38Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block38PowerCoefficients) i := by
  decide +kernel

theorem block38_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block38PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block38Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block38PowerCoefficients
      block38Margin1 (by norm_num) block38_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block38Margin2 : ℚ := (4133051001071607230533232717356669969912418359962812246638519086586902573132740609003469807 : ℚ) / 13743895347200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block38_coefficient_bound_2 : ∀ i : Fin 37, block38Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block38PowerCoefficients) i := by
  decide +kernel

theorem block38_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block38PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block38Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block38PowerCoefficients
      block38Margin2 (by norm_num) block38_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block38Margin3 : ℚ := (4471294382721233925501910067953162826704525123448733466652742709571334 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block38_coefficient_bound_3 : ∀ i : Fin 37, block38Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block38PowerCoefficients) i := by
  decide +kernel

theorem block38_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block38PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block38Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block38PowerCoefficients
      block38Margin3 (by norm_num) block38_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block38Margin4 : ℚ := (447460723462379463799295364771155783091939235874099172809607919865262284513 : ℚ) / 2167568841970223677440000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block38_coefficient_bound_4 : ∀ i : Fin 37, block38Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block38PowerCoefficients) i := by
  decide +kernel

theorem block38_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block38PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block38Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block38PowerCoefficients
      block38Margin4 (by norm_num) block38_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block38Margin5 : ℚ := (6888493166494831817297367116075745559409747827063952854906188699165 : ℚ) / 33056565380087516495872

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block38_coefficient_bound_5 : ∀ i : Fin 37, block38Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block38PowerCoefficients) i := by
  decide +kernel

theorem block38_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block38PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block38Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block38PowerCoefficients
      block38Margin5 (by norm_num) block38_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block38Margin6 : ℚ := (332466265492173587826020442590905664618612075008688188431323665964982671378634429 : ℚ) / 1400000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block38_coefficient_bound_6 : ∀ i : Fin 37, block38Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block38PowerCoefficients) i := by
  decide +kernel

theorem block38_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block38PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block38Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block38PowerCoefficients
      block38Margin6 (by norm_num) block38_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block38Margin7 : ℚ := (4059689556781904170493822685318722972593075194996481171947277730078637193602702016842466527 : ℚ) / 13743895347200000000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block38_coefficient_bound_7 : ∀ i : Fin 37, block38Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block38PowerCoefficients) i := by
  decide +kernel

theorem block38_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block38PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block38Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block38PowerCoefficients
      block38Margin7 (by norm_num) block38_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block38Margin8 : ℚ := (7803640041118111547953369629911305191519910162136961682315433684189184 : ℚ) / 20372681319713592529296875

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block38_coefficient_bound_8 : ∀ i : Fin 37, block38Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block38PowerCoefficients) i := by
  decide +kernel

theorem block38_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block38PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block38Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block38PowerCoefficients
      block38Margin8 (by norm_num) block38_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block38_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block38PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block38_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block38_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block38_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block38_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block38_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block38_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block38_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block38_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block38_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
