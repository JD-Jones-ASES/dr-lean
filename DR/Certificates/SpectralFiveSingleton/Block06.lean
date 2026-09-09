import DR.Certificates.BernsteinTransform
import Mathlib.Data.Fin.VecNotation

/-! Exact transformed coefficient checks for singleton x/y Bernstein block (0,6). -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators

def block06PowerCoefficients : Fin 37 → ℚ := ![(1836152950739769699228127900800000000000000000 : ℚ) / 1, (-17801644130397139452113961379968000000000000000 : ℚ) / 1, (107330003856071909809823479135611000000000000000 : ℚ) / 1, (-380433756551975277085118508052661475000000000000 : ℚ) / 1, (910829057390742473579008972225000842578125000000 : ℚ) / 1, (-1477668748545001550627068489364035181542968750000 : ℚ) / 1, (1662126663763185337028015426800656714160156250000 : ℚ) / 1, (-1227909357578427058335473418575512125600585937500 : ℚ) / 1, (663428541522038503391089094543518799565429687500 : ℚ) / 1, (-393779665791479891525496868635447353633789062500 : ℚ) / 1, (380604715679929970177720043042005058764648437500 : ℚ) / 1, (-41923496890516278731274518172188136449101562500 : ℚ) / 1, (-292115430162571468210573617389700149277578125000 : ℚ) / 1, (323368625060119045067433519769007965605101562500 : ℚ) / 1, (3466769916363408383892615802214083106671875000 : ℚ) / 1, (-82500323011810011310259029767503086613562500000 : ℚ) / 1, (34234663943997750596478016902032959745210937500 : ℚ) / 1, (4744927172255130801197464909620352785471875000 : ℚ) / 1, (-5491887143343020973658664130716844783873437500 : ℚ) / 1, (2405340049567096876341795612249602070745000000 : ℚ) / 1, (590714916586836280243920987824973933373750000 : ℚ) / 1, (-168005439758390104666155521462942417008325000 : ℚ) / 1, (86178737598310750017774687670354719769150000 : ℚ) / 1, (21935183392355422774103148255039722877610000 : ℚ) / 1, (-7419936753934627356824277900062814250020000 : ℚ) / 1, (-477472242799590740034227507957050042300000 : ℚ) / 1, (323312857986721153944926910515460389225000 : ℚ) / 1, (-10195926405970804355036755268849997987500 : ℚ) / 1, (-5354170100030962436084499020889500552500 : ℚ) / 1, (1320469202920774726334850766233944692500 : ℚ) / 1, (122673763749350169557170453578279412500 : ℚ) / 1, (-15041370187755123671350218078997900000 : ℚ) / 1, (862281761149331719270226943328062500 : ℚ) / 1, (427542612209582077265043765309540000 : ℚ) / 1, (21564649300044710037491242548507500 : ℚ) / 1, (0 : ℚ) / 1, (0 : ℚ) / 1]

def block06Margin0 : ℚ := (80545925579537573445493351327798568774184387731157060103029263165907781723984103505723 : ℚ) / 68719476736000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block06_coefficient_bound_0 : ∀ i : Fin 37, block06Margin0 ≤
    powerToBernstein (affinePowerCoefficients ((0 : ℚ) / 1) ((1 : ℚ) / 20) block06PowerCoefficients) i := by
  decide +kernel

theorem block06_interval_pos_0 (t : ℝ)
    (ht : ((0 : ℚ) / 1 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block06PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block06Margin0])
    (powerPolynomial_box_lower_bound ((0 : ℚ) / 1) ((1 : ℚ) / 20) block06PowerCoefficients
      block06Margin0 (by norm_num) block06_coefficient_bound_0 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block06Margin1 : ℚ := (3306826606310368971581210240679136881221190183184362083132983367865426570063 : ℚ) / 4000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block06_coefficient_bound_1 : ∀ i : Fin 37, block06Margin1 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 20) ((1 : ℚ) / 10) block06PowerCoefficients) i := by
  decide +kernel

theorem block06_interval_pos_1 (t : ℝ)
    (ht : ((1 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block06PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block06Margin1])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 20) ((1 : ℚ) / 10) block06PowerCoefficients
      block06Margin1 (by norm_num) block06_coefficient_bound_1 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block06Margin2 : ℚ := (45544239386727357475376250048121333686795751421312450409829121437251048567393238883667 : ℚ) / 68719476736000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block06_coefficient_bound_2 : ∀ i : Fin 37, block06Margin2 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 10) ((3 : ℚ) / 20) block06PowerCoefficients) i := by
  decide +kernel

theorem block06_interval_pos_2 (t : ℝ)
    (ht : ((1 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block06PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block06Margin2])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 10) ((3 : ℚ) / 20) block06PowerCoefficients
      block06Margin2 (by norm_num) block06_coefficient_bound_2 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block06Margin3 : ℚ := (560860642401312030112825878203687843480499559464826647695722221432 : ℚ) / 931322574615478515625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block06_coefficient_bound_3 : ∀ i : Fin 37, block06Margin3 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 20) ((1 : ℚ) / 5) block06PowerCoefficients) i := by
  decide +kernel

theorem block06_interval_pos_3 (t : ℝ)
    (ht : ((3 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block06PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block06Margin3])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 20) ((1 : ℚ) / 5) block06PowerCoefficients
      block06Margin3 (by norm_num) block06_coefficient_bound_3 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block06Margin4 : ℚ := (44652009189604897206266482224156085950100707398909027818183629418824642313 : ℚ) / 74832610406400000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block06_coefficient_bound_4 : ∀ i : Fin 37, block06Margin4 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 5) ((1 : ℚ) / 4) block06PowerCoefficients) i := by
  decide +kernel

theorem block06_interval_pos_4 (t : ℝ)
    (ht : ((1 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((1 : ℚ) / 4 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block06PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block06Margin4])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 5) ((1 : ℚ) / 4) block06PowerCoefficients
      block06Margin4 (by norm_num) block06_coefficient_bound_4 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block06Margin5 : ℚ := (44588593862332618392338381063937012905084453654317546010762116875 : ℚ) / 73786976294838206464

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block06_coefficient_bound_5 : ∀ i : Fin 37, block06Margin5 ≤
    powerToBernstein (affinePowerCoefficients ((1 : ℚ) / 4) ((3 : ℚ) / 10) block06PowerCoefficients) i := by
  decide +kernel

theorem block06_interval_pos_5 (t : ℝ)
    (ht : ((1 : ℚ) / 4 : ℝ) ≤ t) (ht1 : t ≤ ((3 : ℚ) / 10 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block06PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block06Margin5])
    (powerPolynomial_box_lower_bound ((1 : ℚ) / 4) ((3 : ℚ) / 10) block06PowerCoefficients
      block06Margin5 (by norm_num) block06_coefficient_bound_5 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block06Margin6 : ℚ := (2606483576165906355816827462647818885482533854012970398971206863896071748487 : ℚ) / 4000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block06_coefficient_bound_6 : ∀ i : Fin 37, block06Margin6 ≤
    powerToBernstein (affinePowerCoefficients ((3 : ℚ) / 10) ((7 : ℚ) / 20) block06PowerCoefficients) i := by
  decide +kernel

theorem block06_interval_pos_6 (t : ℝ)
    (ht : ((3 : ℚ) / 10 : ℝ) ≤ t) (ht1 : t ≤ ((7 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block06PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block06Margin6])
    (powerPolynomial_box_lower_bound ((3 : ℚ) / 10) ((7 : ℚ) / 20) block06PowerCoefficients
      block06Margin6 (by norm_num) block06_coefficient_bound_6 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block06Margin7 : ℚ := (51043713204792389943258185522253106210177135914223523119876641704476713019404346245387 : ℚ) / 68719476736000000000000000000000000000000

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block06_coefficient_bound_7 : ∀ i : Fin 37, block06Margin7 ≤
    powerToBernstein (affinePowerCoefficients ((7 : ℚ) / 20) ((2 : ℚ) / 5) block06PowerCoefficients) i := by
  decide +kernel

theorem block06_interval_pos_7 (t : ℝ)
    (ht : ((7 : ℚ) / 20 : ℝ) ≤ t) (ht1 : t ≤ ((2 : ℚ) / 5 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block06PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block06Margin7])
    (powerPolynomial_box_lower_bound ((7 : ℚ) / 20) ((2 : ℚ) / 5) block06PowerCoefficients
      block06Margin7 (by norm_num) block06_coefficient_bound_7 t (by norm_num at *; exact ⟨ht, ht1⟩))

def block06Margin8 : ℚ := (828513033646361578960802807185125117036616993383432998919897090048 : ℚ) / 931322574615478515625

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem block06_coefficient_bound_8 : ∀ i : Fin 37, block06Margin8 ≤
    powerToBernstein (affinePowerCoefficients ((2 : ℚ) / 5) ((9 : ℚ) / 20) block06PowerCoefficients) i := by
  decide +kernel

theorem block06_interval_pos_8 (t : ℝ)
    (ht : ((2 : ℚ) / 5 : ℝ) ≤ t) (ht1 : t ≤ ((9 : ℚ) / 20 : ℝ)) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block06PowerCoefficients) := by
  exact lt_of_lt_of_le (by norm_num [block06Margin8])
    (powerPolynomial_box_lower_bound ((2 : ℚ) / 5) ((9 : ℚ) / 20) block06PowerCoefficients
      block06Margin8 (by norm_num) block06_coefficient_bound_8 t (by norm_num at *; exact ⟨ht, ht1⟩))

/-- Positivity on the complete closed physical certificate interval. -/
theorem block06_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9 / 20) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial block06PowerCoefficients) := by
  by_cases h0 : t ≤ (1 : ℝ) / 20
  · exact block06_interval_pos_0 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h1 : t ≤ (2 : ℝ) / 20
  · exact block06_interval_pos_1 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h2 : t ≤ (3 : ℝ) / 20
  · exact block06_interval_pos_2 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h3 : t ≤ (4 : ℝ) / 20
  · exact block06_interval_pos_3 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h4 : t ≤ (5 : ℝ) / 20
  · exact block06_interval_pos_4 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h5 : t ≤ (6 : ℝ) / 20
  · exact block06_interval_pos_5 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h6 : t ≤ (7 : ℝ) / 20
  · exact block06_interval_pos_6 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  by_cases h7 : t ≤ (8 : ℝ) / 20
  · exact block06_interval_pos_7 t (by norm_num at *; linarith) (by norm_num at *; linarith)
  exact block06_interval_pos_8 t (by norm_num at *; linarith) (by norm_num at *; linarith)

end
end DittertRybin.Certificates.SpectralFiveSingleton
